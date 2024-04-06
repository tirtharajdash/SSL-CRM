import random

import numpy as np
import torch
from torch import nn
from ray import tune
from ray.tune.schedulers import AsyncHyperBandScheduler
#from ray.tune.suggest.basic_variant import BasicVariantGenerator
from ray.tune.search.basic_variant import BasicVariantGenerator
from sklearn.model_selection import train_test_split
from tqdm.auto import tqdm, trange

from crm.core import Network
from crm.utils import get_metrics, save_object, get_autoencoder_metrics
import time

def train(
    n: Network,
    X_train,
    y_train,
    num_epochs: int,
    optimizer: torch.optim.Optimizer,
    criterion,
    save_here: str = None,
    X_val=None,
    y_val=None,
    batch_size: int = 32,
    verbose: bool = False,
    save_atepoch: int = 20,
    device = torch.device("cpu"),

):
    # train_losses = []
    # val_losses = []
    # train_accs = []
    # val_accs = []
    # min_loss = 1e10
    # train_time = []
    # for e in trange(num_epochs):
    #     start = time.time()
    #     c = list(zip(X_train, y_train))
    #     random.shuffle(c)
    #     X_train, y_train = zip(*c)
    #     local_train_losses = []
    #     for i in trange(len(X_train)):

    #         # print(f"Epoch {e}/{num_epochs} | Batch {i}/{len(X_train)}")
    #         f_mapper = X_train[i]
    #         input_layerwise = ([torch.tensor([f_mapper[neuron] for neuron in neurons], dtype = torch.float32) for neurons in n.layers_list]) #input for new implementation
    #         # if i <= 3:
    #         #         print(f"\n\nModel initialized params for {i}:")
    #         #         for name, param in n.named_parameters():
    #         #             print(name, param.data.shape, param.data)
    #         out = n.forward(input_layerwise).reshape(1, -1)
            
    train_losses = []
    val_losses = []
    train_accs = []
    val_accs = []
    min_loss = 1e10
    num_batches = len(X_train) // batch_size
    train_time = []
    for e in trange(num_epochs):
        start = time.time()
        c = list(zip(X_train, y_train))
        random.shuffle(c)
        X_train, y_train = zip(*c)
        local_train_losses = []
        for i in trange(num_batches):
            start_idx = i * batch_size
            end_idx = (i + 1) * batch_size
            batch_X = [[sample[i] for i in range(len(sample))] for sample in X_train[start_idx:end_idx]] # change to sample.values() <------
            batch_y = y_train[start_idx:end_idx]
            batch_X = torch.tensor(batch_X, dtype=torch.float32).to(device)
            batch_y = torch.tensor(batch_y, dtype=torch.long).to(device)
            input_layerwise = ([torch.stack([batch_X[:, neuron] for neuron in neurons], dim = -1) for neurons in n.layers_list]) #input for new implementation
            #print(f"input_layerwise 0: {input_layerwise[0].shape}")
            #quit()
            out = n.forward(input_layerwise).reshape(batch_size, -1)
            target = batch_y.reshape(batch_size)
            
            # print(f"tagret d_type: {target.dtype}")
            # print(f"out d_type: {out.dtype}")
            # print(f"tagret shape: {target.shape}")
            # print(f"out shape: {out.shape}")
            # quit()
            #print(f"model layers:\n {n.layerwise_neurons}")
            #print(f"\n\nShapes:\ny_train = {y_train[i].reshape(1)},\nout = {out.reshape(1)},\n")
            loss = criterion(out, target)
            local_train_losses.append(loss.item())

            loss.backward()
            # if i % 100 == 0:
            #     for param in n.parameters():
            #         print(f"\nOld params:\n{param.data}\n")
            #         print(f"\nGrads:\n{param.grad}\n")            
            optimizer.step()

            # if i % 100 == 0:
                # for param in n.parameters():
                #     print(f"\nNew params:\n{param.data}\n")
            optimizer.zero_grad()
            #n.reset()
        with torch.no_grad():
            train_losses.append(sum(local_train_losses) / len(local_train_losses))
            train_accs.append(
                get_metrics(n, X_train, y_train, output_dict=True)["accuracy"]
            )
            if X_val is not None and y_val is not None:
                local_val_losses = []
                for j in range(len(X_val)):
                    f_mapper = X_val[j]
                    input_layerwise = ([torch.tensor([f_mapper[neuron] for neuron in neurons], dtype = torch.float32).to(device) for neurons in n.layers_list]) #input for new implementation
                    out = n.forward(input_layerwise).reshape(1, -1)
                    target = torch.tensor([y_val[j]], dtype = torch.long).to(device).reshape(1)
                    loss = criterion(out, target)
                    local_val_losses.append(loss.item())
                    #n.reset()
                val_losses.append(sum(local_val_losses) / len(local_val_losses))
                val_accs.append(
                    get_metrics(n, X_val, y_val, output_dict=True)["accuracy"]
                )
                if val_losses[-1] < min_loss:
                    min_loss = val_losses[-1]
                    patience = 0
                else:
                    patience += 1
                if patience > 3:
                    print("Patience exceeded. Stopping training.")
                    break
        if verbose:
            tqdm.write(f"Epoch {e}")
            tqdm.write(f"Train loss: {train_losses[-1]}")
            tqdm.write(f"Train acc: {train_accs[-1]}")
            if X_val is not None and y_val is not None:
                tqdm.write(f"Val loss: {val_losses[-1]}")
                tqdm.write(f"Val acc: {val_accs[-1]}")
            tqdm.write("-------------------------------------")
        if e % save_atepoch == 0:
            if save_here is not None:
                save_object(n, f"{save_here}_{e}.pt")
    if save_here is not None:
        save_object(n, f"{save_here}_{e}.pt")
    return (
        (train_losses, train_accs, val_losses, val_accs)
        if X_val is not None and y_val is not None
        else (train_losses, train_accs, None, None)
    )


def train_autoencoder(
    n: Network,
    n_decoder: nn.Module,
    X_train,
    y_train,
    num_epochs: int,
    optimizer: torch.optim.Optimizer,
    criterion,
    save_here: str = None,
    X_val=None,
    y_val=None,
    batch_size: int = 32,
    verbose: bool = False,
    save_atepoch: int = 20,
    device = torch.device("cpu"),
    
):
    train_losses = []
    val_losses = []
    train_accs = []
    val_accs = []
    min_loss = 1e10
    num_batches = len(X_train) // batch_size
    for e in trange(num_epochs):
        c = list(zip(X_train, y_train))
        random.shuffle(c)
        X_train, y_train = zip(*c)
        local_train_losses = []
        for i in trange(num_batches):
            start_idx = i * batch_size
            end_idx = (i + 1) * batch_size
            batch_X = [[sample[i] for i in range(len(sample))] for sample in X_train[start_idx:end_idx]] # change to sample.values() <------
            #batch_y = y_train[start_idx:end_idx]
            batch_X = torch.tensor(batch_X, dtype=torch.float32).to(device)
            
            #batch_y = torch.tensor(batch_y, dtype=torch.float32)
            input_layerwise = ([torch.stack([batch_X[:, neuron] for neuron in neurons], dim = -1) for neurons in n.layers_list]) #input for new implementation
            #print(f"input_layerwise 0: {input_layerwise[0].shape}")
            #quit()
            out_encoder = n.forward(input_layerwise).reshape(batch_size, -1)
            out = n_decoder.forward(out_encoder)
            target = input_layerwise[0]

            loss = criterion(out, target)
            local_train_losses.append(loss.item())
            loss.backward()
            optimizer.step()
            optimizer.zero_grad()

        with torch.no_grad():
            train_losses.append(sum(local_train_losses) / len(local_train_losses))
            train_accs.append(get_autoencoder_metrics(n, n_decoder, X_train, output_dict=True))
            #print(f"Train acc: {train_accs[-1]}")
            if X_val is not None:
                local_val_losses = []
                for j in range(len(X_val)):
                    f_mapper = X_val[j]
                    input_layerwise = ([torch.tensor([f_mapper[neuron] for neuron in neurons], dtype = torch.float32).to(device) for neurons in n.layers_list]) #input for new implementation

                    out_encoder = n.forward(input_layerwise).reshape(1, -1)
                    out = n_decoder.forward(out_encoder)
                    target = torch.tensor([X_train[i][j] for j in range(len(n.layers_list[0]))], dtype = torch.float32).to(device).reshape(1, -1)
                    loss = criterion(out, target)
                    local_val_losses.append(loss.item())
                val_losses.append(sum(local_val_losses) / len(local_val_losses))
                val_accs.append(get_autoencoder_metrics(n, n_decoder, X_val, output_dict=True))
                if val_losses[-1] < min_loss:
                    min_loss = val_losses[-1]
                    patience = 0
                else:
                    patience += 1
                if patience > 3:
                    print("Patience exceeded. Stopping training.")
                    break
                
        if verbose:
            tqdm.write(f"Epoch {e}")
            tqdm.write(f"Train loss: {train_losses[-1]}")
            tqdm.write(f"Train acc: {train_accs[-1]}")
            if X_val is not None:
                tqdm.write(f"Val loss: {val_losses[-1]}")
                tqdm.write(f"Val acc: {val_accs[-1]}")
            tqdm.write("-------------------------------------")
        if e % save_atepoch == 0:
            if save_here is not None:
                save_object(n, f"{save_here}_{e}.pt")
    if save_here is not None:
        save_object(n, f"{save_here}_{e}.pt")
    return (
        (train_losses, train_accs, val_losses, val_accs)
        if X_val is not None and y_val is not None
        else (train_losses, train_accs, None, None)
    )

def get_best_config(
    n: Network,
    X,
    y,
    num_epochs: int,
    optimizer: torch.optim.Optimizer,
    criterion,
):
    """Uses Ray Tune and Optuna to find the best configuration for the network."""

    def train_with_config(config):
        """Train the network with the given config."""
        optimizer = torch.optim.Adam(n.parameters(), lr=config["lr"])
        X_train, X_val, y_train, y_val = train_test_split(
            X, y, test_size=0.2, random_state=24, stratify=y
        )
        train_losses, train_accs, val_losses, val_accs = train(
            n=n,
            X_train=X_train,
            y_train=y_train,
            num_epochs=num_epochs,
            optimizer=optimizer,
            criterion=criterion,
            X_val=X_val,
            y_val=y_val,
            verbose=False,
        )
        return {
            "mean_train_loss": np.mean(train_losses),
            "mean_train_acc": np.mean(train_accs),
            "mean_val_loss": np.mean(val_losses),
            "mean_val_acc": np.mean(val_accs),
        }

    config = {"lr": tune.grid_search([0.01, 0.001, 0.005, 0.0001])}
    algo = BasicVariantGenerator(max_concurrent=16)
    # uncomment and set max_concurrent to limit number of cores
    # algo = ConcurrencyLimiter(algo, max_concurrent=16)
    scheduler = AsyncHyperBandScheduler()

    analysis = tune.run(
        train_with_config,
        num_samples=1,
        config=config,
        name="optuna_train",
        metric="mean_val_acc",
        mode="max",
        search_alg=algo,
        scheduler=scheduler,
        verbose=0,
        max_failures=1,
    )

    return analysis.best_config
