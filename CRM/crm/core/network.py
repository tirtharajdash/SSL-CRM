from itertools import repeat
from typing import Callable

import torch
from torch import nn
import torch.nn.functional as F
import torch.multiprocessing as mp
from torch.multiprocessing import Pool

from crm.core import Neuron

import torch
from torch import nn
import torch.nn.functional as F
import torch.optim as optim

import torch
import torch.nn as nn

import torch
from torch import nn
import torch.nn.functional as F
import torch.optim as optim

import torch
import torch.nn as nn

class rho_2_layer(nn.Module):
    num_layers = 0
    def __init__(self, layer_input_size, layer_output_size, model_input_size, neuron_mask_0, neuron_mask_prev, bias = False):
        super(rho_2_layer, self).__init__()
        rho_2_layer.num_layers += 1
        self.in_features = layer_input_size
        self.in_features_model = model_input_size
        self.out_features = layer_output_size
        self.layer_id = rho_2_layer.num_layers
        self.layer_0 = nn.Linear(model_input_size, layer_output_size, bias=False)
        self.layer_prev = nn.Linear(layer_input_size, layer_output_size, bias=False)
        self.activation = nn.ReLU()
        self.neuron_mask_0 = neuron_mask_0
        self.neuron_mask_prev = neuron_mask_prev
        # print(f"\nneuron_mask_0: {neuron_mask_prev.shape, neuron_mask_prev.sum()}")
        # print(f"neuron_mask_prev: {neuron_mask_prev.shape, neuron_mask_prev.sum()}")
        self.bias = 0
        if bias == True:
            self.bias = torch.nn.Parameter(torch.zeros(layer_output_size,))
        # self.layer_0.weight = torch.nn.Parameter(self.layer_0.weight * self.neuron_mask_0)
        # self.layer_prev.weight = torch.nn.Parameter(self.layer_prev.weight * self.neuron_mask_prev)
                
    def forward(self, x, input_layer):
        #print(f"sizes of parameter and mask of layer_0: {self.layer_0.weight.shape, self.neuron_mask_0.shape}")
        #print(f"sizes of parameter and mask of layer_prev: {self.layer_prev.weight.shape, self.neuron_mask_prev.shape}")
        self.layer_0.weight.item = (self.layer_0.weight * self.neuron_mask_0)
        self.layer_prev.weight.item = (self.layer_prev.weight * self.neuron_mask_prev)
        
        layer_out_0 = self.layer_0(input_layer) 
        layer_out_prev = self.layer_prev(x)
        activation_out = self.activation(layer_out_0 + layer_out_prev + self.bias)
        return activation_out
    
class rho_1_layer(nn.Module):
    num_layers = 0
    def __init__(self, layer_input_size, layer_output_size, neuron_mask_prev, bias = False):
        super(rho_1_layer, self).__init__()
        rho_1_layer.num_layers += 1
        self.in_features = layer_input_size
        self.out_features = layer_output_size
        self.layer_id = rho_1_layer.num_layers
        self.layer_prev = nn.Linear(layer_input_size, layer_output_size, bias=False)
        self.activation = nn.ReLU()
        self.neuron_mask_prev = neuron_mask_prev
        # print(f"\nneuron_mask_prev: {neuron_mask_prev.shape, neuron_mask_prev.sum()}")
        self.bias = 0
        if bias == True:
            self.bias = torch.nn.Parameter(torch.zeros(layer_output_size,))
        #self.layer_prev.weight = torch.nn.Parameter(self.layer_prev.weight * self.neuron_mask_prev)

                
    def forward(self, x):
        self.layer_prev.weight.item = (self.layer_prev.weight * self.neuron_mask_prev)

        layer_out_prev = self.layer_prev(x)
        activation_out = self.activation(layer_out_prev + self.bias)
        return activation_out
    
class CRM_model(nn.Module):
    def __init__(self, num_neurons, adj_list, include_top = True,
                 ajd_matrix = True, output_layer = False, bias = False, device = torch.device("cpu")):
        super(CRM_model, self).__init__()
        self.num_neurons = num_neurons
        self.bias = bias
        self.adj_list = adj_list
        self.adj_matrix = None
        if ajd_matrix:
            self.adj_matrix = self._get_adjacency_matrix()
        self.layers_list = self._get_layers_list()
        #print(f"layerwise distribution:\n{[len(layer) for layer in self.layers_list]}\n")
        #print(f"num neurons (sum, real):\n{sum([len(layer) for layer in self.layers_list]), num_neurons}\n")
        #self.layers_list = layers_list
        if self.adj_matrix is not None:
            self.d_rho2, self.d_rho1 = self._get_rho_vals()
        else:
            self.d_rho2, self.d_rho1 = 1, 0
        self.input_size = len(self.layers_list[0])
        self.output_size = len(self.layers_list[-1])
    
        self.device = device
        self.layers = self._setup_layers()
        if not include_top:
            self.layers.pop(-1)
            self.layers_list.pop(-1)
        if output_layer:
            self.layers.append(nn.Linear(self.layers[-1].out_features, 2, bias=self.bias))
        #self.layers[-1].activation = nn.Sigmoid()
        self.myparameters = nn.ParameterList(self.layers)   
        
        # print(f"layers:\n{self.layers}\n")
        # print(f"layerwise distribution:\n{[len(layer) for layer in self.layers_list]}\n")
        # print(f"num neurons (real - layerwise):\n{sum([len(layer) for layer in self.layers_list])}\n")
        # print(f"num neurons (real - adj_list):\n{len(self.adj_list)}\n")
        # print(f"num neurons (args):\n{self.num_neurons}\n")
        # print(f"d_rho2, d_rho1:\n{self.d_rho2, self.d_rho1}\n")
        # quit() 
        
    def forward(self, input_layerwise):
        x = input_layerwise[0]
        input_layer = input_layerwise[0]
        for i, layer in enumerate(self.layers):
            #print(f"For layer {i+1}, the input is {x.shape}")
            if isinstance(layer, rho_2_layer):
                x = layer(x, input_layer)  * input_layerwise[i+1]
            elif isinstance(layer, rho_1_layer):
                x = layer(x) * input_layerwise[i+1]
            else: 
                x = layer(x)
        return x
                
    def _get_layers_list(self):
        layer_list = []
        prev_neurons = set()
        current_layer_neurons = []
        last_layer = []
        #print(len(self.adj_list))
        for i in range(len(self.adj_list)):
            if self.adj_list[i] == []:
                last_layer.append(i)
            
            else:
                if i in prev_neurons:
                    prev_neurons = set()
                    layer_list.append(current_layer_neurons)
                    current_layer_neurons = []
                
                current_layer_neurons.append(i)
                prev_neurons = prev_neurons.union(set(self.adj_list[i]))
        layer_list.append(current_layer_neurons)
        layer_list.append(last_layer)

        return layer_list
        
    def _get_adjacency_matrix(self):
        # Create adjacency matrix using an adjacency list
        adj_matrix = torch.zeros(self.num_neurons, self.num_neurons)
        for i in range(self.num_neurons):
            if self.adj_list[i]:
                adj_matrix[i][self.adj_list[i]] = 1
        return adj_matrix
    
    def _get_rho_vals(self):
        d_rho1, d_rho_2 = 0, 0
        for layer in self.layers_list[1:-1]:
            if sum(self.adj_matrix[:, layer[0]]) == 1:
                d_rho1 += 1
            elif sum(self.adj_matrix[:, layer[0]]) == 2:
                d_rho_2 += 1
            else:
                raise Exception("Invalid layer")
        return d_rho1, d_rho_2
    
    def _get_submask(self, layer_in, layer_out):
        if self.adj_matrix is not None:
            return self.adj_matrix[self.layers_list[layer_in]][:, self.layers_list[layer_out]].T
    
        else:
            layer_in = self.layers_list[layer_in]
            layer_out = self.layers_list[layer_out]
            sub_mask = torch.zeros(len(layer_in), len(layer_out))
            for i in range(len(layer_in)):
                for j in range(len(layer_out)):
                    if layer_out[j] in self.adj_list[layer_in[i]]:
                        sub_mask[i][j] = 1
            return sub_mask.T.to(self.device)
    
        
    def _set_neuron_masks(self):
        # Create neuron masks for each layer based on the adjacency matrix
        neuron_masks = []
        for i in range(self.num_neurons):
            neuron_masks.append(self.adj_matrix[i])
        return neuron_masks
    
    def _setup_layers(self):
        # Creates a list of all layers
        layers = []
        for i in range(self.d_rho2 + self.d_rho1 + 1):
            if i == 0:
                layers.append(rho_1_layer(len(self.layers_list[i]),
                                          len(self.layers_list[i+1]), 
                                          self._get_submask(i, i+1),
                                          bias=self.bias,
                                          ))
            elif i < self.d_rho2:
                layers.append(rho_2_layer(len(self.layers_list[i]), 
                                          len(self.layers_list[i+1]), 
                                          self.input_size,
                                          self._get_submask(0, i+1),
                                          self._get_submask(i, i+1),
                                          bias=self.bias
                                          ))
            else:
                layers.append(rho_1_layer(len(self.layers_list[i]),
                                          len(self.layers_list[i+1]), 
                                          self._get_submask(i, i+1),
                                          bias=self.bias,
                                          ))
        return layers
    
    def lrp(self, inputs):
        # LRP for the model
        pass
    

# from torch.multiprocessing.pool import ThreadPool
class Decoder_fullyconnected(nn.Module):
    def __init__(self, n, bias = True):
        super().__init__()
        # print(f"n.layers_list: {[len(layer) for layer in n.layers_list]}")
        self.layers = [nn.Linear(len(n.layers_list[i]), len(n.layers_list[i-1]), bias = bias) for i in range(len(n.layers_list)-1, 0, -1)]
        self.myparameters = nn.ParameterList(self.layers)   
        # print(f"layers: {self.layers}")
        # for i in range(n.num_layers - 1):
        #     if i == 0:
        #         self.layers.append(nn.Linear(len(n.layerwise_neurons[n.num_layers - 2]), len(n.layerwise_neurons[1])))
        #     elif i == n.num_layers - 2:
        #         self.layers.append(nn.Linear(len(n.layerwise_neurons[n.num_layers - 2]), len(n.layerwise_neurons[0])))
        #     else:
        #         self.layers.append(nn.Linear(len(n.layerwise_neurons[i]), len(n.layerwise_neurons[i+1])))
                
    def forward(self, x):
        for layer in self.layers:
            x = F.relu(layer(x))
        x = F.sigmoid(x)
        return x
        
        
class Network:
    def __init__(self, num_neurons, adj_list, custom_activations=None):
        self.num_neurons = num_neurons
        self.adj_list = adj_list
        self.neurons = [
            Neuron(i)
            if custom_activations is None
            else Neuron(i, custom_activations[i][0], custom_activations[i][1])
            for i in range(num_neurons)
        ]
        self.num_layers = 1
        self.weights = self._set_weights()
        self.topo_order = self._topological_sort()
        self._setup_neurons()
        self._set_output_neurons()
        self._assign_layers()
        self._set_layerwise_neurons()
        self.has_forwarded = False
        self.is_fresh = True

    def _forward_layer(self, n_id, f_mapper, queue):

        # print(n_id, f_mapper)

        # print(f"Forwarding {n_id}")
        if self.neurons[n_id].predecessor_neurons:
            for pred in self.neurons[n_id].predecessor_neurons:
                # print(f"Predecessor {pred} = {self.neurons[pred].value}")
                self.neurons[n_id].value = self.neurons[n_id].value + (
                    self.weights[(pred, n_id)] * self.neurons[pred].value
                )
            # print(f"New Value: {n_id} = {self.neurons[n_id].value}")
            self.neurons[n_id].value = f_mapper[n_id] * self.neurons[
                n_id
            ].activation_fn(self.neurons[n_id].value)
        else:
            self.neurons[n_id].value = f_mapper[n_id]
        if type(self.neurons[n_id].value) == torch.Tensor:
            queue.put((n_id, self.neurons[n_id].value.detach()))
        else:
            queue.put((n_id, self.neurons[n_id].value))
        # print(f"FINAL: {n_id} = {self.neurons[n_id].value}")

    def fast_forward(self, f_mapper):
        """Fast forward the network with the given inputs"""
        if not self.is_fresh:
            raise Exception(
                "Network has already been forwarded. You may want to reset it."
            )
        self.has_forwarded = True
        self.is_fresh = False

        layer_mapper = [[] for _ in range(self.num_layers)]
        for n_id in self.topo_order:
            layer_mapper[self.neurons[n_id].layer].append(n_id)

        manager = mp.Manager()
        queue = manager.Queue()

        # pool_tuple =

        # print(layer_mapper)
        pool = Pool(mp.cpu_count())
        for layer in range(self.num_layers):
            pool.starmap(
                self._forward_layer,
                zip(layer_mapper[layer], repeat(f_mapper), repeat(queue)),
            )
            while not queue.empty():
                n_id, value = queue.get()
                # print(f"{n_id} = {value}")
                self.neurons[n_id].value = value
        pool.close()
        pool.join()

        return torch.stack([self.neurons[i].value for i in self.output_neurons])

    def forward(self, f_mapper):
        if not self.is_fresh:
            raise Exception(
                "Network has already been forwarded. You may want to reset it."
            )
        self.has_forwarded = True
        self.is_fresh = False
        for n_id in self.topo_order:
            if self.neurons[n_id].predecessor_neurons:
                for pred in self.neurons[n_id].predecessor_neurons:
                    self.neurons[n_id].value = self.neurons[n_id].value + (
                        self.weights[(pred, n_id)] * self.neurons[pred].value
                    )
                self.neurons[n_id].value = f_mapper[n_id] * self.neurons[
                    n_id
                ].activation_fn(self.neurons[n_id].value)
            else:
                self.neurons[n_id].value = f_mapper[n_id]

        return (torch.stack([self.neurons[i].value for i in self.output_neurons]))
        #return torch.stack([neuron.value for neuron in self.neurons if neuron.layer == self.num_layers - 2])

    def forward_1(self, f_mapper):
        if not self.is_fresh:
            raise Exception(
                "Network has already been forwarded. You may want to reset it."
            )
        self.has_forwarded = True
        self.is_fresh = False
        for n_id in self.topo_order:
            if self.neurons[n_id].predecessor_neurons:
                for pred in self.neurons[n_id].predecessor_neurons:
                    self.neurons[n_id].value = self.neurons[n_id].value + (
                        self.weights[(pred, n_id)] * self.neurons[pred].value
                    )
                self.neurons[n_id].value = f_mapper[n_id] * self.neurons[
                    n_id
                ].activation_fn(self.neurons[n_id].value)
            else:
                self.neurons[n_id].value = f_mapper[n_id]

        #return torch.stack([self.neurons[i].value for i in self.output_neurons])
        return torch.stack([neuron.value for neuron in self.neurons if neuron.layer == self.num_layers - 2])

    def parameters(self):
        return (p for p in self.weights.values())

    def set_neuron_activation(
        self,
        n_id: int,
        activation_fn: Callable,
    ):
        self.neurons[n_id].set_activation_fn(activation_fn)

    def reset(self):
        for n in self.neurons:
            n.value = 0
            n.grad = 0
            n.relevance = 0
        self.is_fresh = True

    def to(self, device):
        # https://discuss.pytorch.org/t/tensor-to-device-changes-is-leaf-causing-cant-optimize-a-non-leaf-tensor/37659
        for key, value in self.weights.items():
            self.weights[key] = (
                self.weights[key].to(device).detach().requires_grad_(True)
            )

    def get_weights(self):
        return self.weights

    def set_weights(self, weights):
        self.weights = weights

    def get_gradients(self):
        grads = []
        for p in self.parameters():
            grad = None if p.grad is None else p.grad.data.cpu().numpy()
            grads.append(grad)
        return grads

    def set_gradients(self, gradients):
        for g, p in zip(gradients, self.parameters()):
            if g is not None:
                p.grad = torch.from_numpy(g)

    def _set_output_neurons(self):
        self.output_neurons = []
        for n in self.neurons:
            if len(n.successor_neurons) == 0:
                self.output_neurons.append(n.n_id)
                
    def _set_layerwise_neurons(self):
        self.layerwise_neurons = {i:[] for i in range(self.num_layers)}
        for neuron in self.neurons:
            self.layerwise_neurons[neuron.layer].append(neuron.n_id)
        

    def _setup_neurons(self):
        rev_adj_list = [[] for _ in range(self.num_neurons)]
        for i in range(self.num_neurons):
            for e in self.adj_list[i]:
                rev_adj_list[e].append(i)
        for u in self.neurons:
            u.set_successor_neurons(self.adj_list[u.n_id])
        for v in self.neurons:
            v.set_predecessor_neurons(rev_adj_list[v.n_id])

    def _set_weights(self):
        """
        This function sets the weights of the network.
        """
        weights = {}
        for u in range(self.num_neurons):
            for v in self.adj_list[u]:
                weights[(u, v)] = torch.rand(1, requires_grad=True)
        return weights

    def _topological_sort_util(self, v, visited, stack):
        # Mark the current node as visited.
        visited[v] = True

        # Recur for all the vertices adjacent to this vertex
        for i in self.adj_list[v]:
            if visited[i] is False:
                self._topological_sort_util(i, visited, stack)

        # Push current vertex to stack which stores result
        stack.append(v)

    def _topological_sort(self):
        """Returns the topological sorted order of a graph"""
        visited = [False] * self.num_neurons
        stack = []
        for i in range(self.num_neurons):
            if visited[i] is False:
                self._topological_sort_util(i, visited, stack)
        return stack[::-1]

    def _assign_layers(self):
        """Assigns layers to neurons of the network"""
        for n in self.neurons:
            if len(n.predecessor_neurons) == 0:
                n.layer = 0

        for n_id in self.topo_order:
            if len(self.neurons[n_id].predecessor_neurons) > 0:
                self.neurons[n_id].layer = (
                    max(
                        [
                            self.neurons[i].layer
                            for i in self.neurons[n_id].predecessor_neurons
                        ]
                    )
                    + 1
                )
                self.num_layers = max(self.num_layers, self.neurons[n_id].layer + 1)

    def lrp(self, R, n_id):
        for n in self.neurons:
            if n.relevance != 0:
                raise Exception("Relevances are not cleared, try reseting the network")
        self.neurons[n_id].relevance = R
        for n_id in self.topo_order[::-1]:
            for succ in self.neurons[n_id].successor_neurons:
                my_contribution = 1e-9
                total_contribution = 1e-9
                for pred in self.neurons[succ].predecessor_neurons:
                    if pred == n_id:
                        my_contribution = (
                            self.neurons[n_id].value * self.weights[(pred, succ)]
                        )
                        total_contribution += my_contribution
                    else:
                        total_contribution += (
                            self.neurons[pred].value * self.weights[(pred, succ)]
                        )

                self.neurons[n_id].relevance += (
                    self.neurons[succ].relevance * my_contribution / total_contribution
                )
                
