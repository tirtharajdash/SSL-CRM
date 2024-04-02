import random

import dill
import torch
from sklearn.metrics import classification_report


def save_object(obj, filename):
    with open(filename, "wb") as outp:  # Overwrites any existing file.
        dill.dump(obj, outp, dill.HIGHEST_PROTOCOL)


def load_object(filename):
    with open(filename, "rb") as inp:
        return dill.load(inp)


def get_metrics(n, X_test, y_test, output_dict=False):
   
    y_pred = []
    for inp in X_test:
        # print(inp)
        inp = [torch.tensor([inp[neuron] for neuron in neurons], dtype = torch.float32) for neurons in n.layers_list] #for new implementation
        out = n.forward(inp)
        # if inp == X_test[0]:
        #     print(f"out: {out.shape}")
        y_pred.append(torch.argmax(out))
    
    # print(f"y_pred: {out.shape}")
    # print(f"y_pred unique: {(set(map(float, y_pred)))}")
    # print(f"y_test unique: {(set(map(float, y_test)))}")        #n.reset()
        
        
    return classification_report(
        torch.stack(y_test).numpy(),
        torch.tensor(y_pred).numpy(),
        digits=4,
        output_dict=output_dict,
        zero_division=0,
    )
    
def get_autoencoder_metrics(n, n_decoder, X_test, output_dict=False):
    with torch.no_grad():
        batch_X = [[sample[i] for i in range(len(sample))] for sample in X_test] # change to sample.values() <------
        batch_X = torch.tensor(batch_X, dtype=torch.float32)
        input_layerwise = ([torch.stack([batch_X[:, neuron] for neuron in neurons], dim = -1) for neurons in n.layers_list]) #input for new implementation
        out_encoder = n.forward(input_layerwise).reshape(batch_X.shape[0], -1)
        out = n_decoder.forward(out_encoder) > 0.5
        target = input_layerwise[0]
        accuracy = sum([out[i] == target[i] for i in range(out.shape[0])]) / out.shape[0]
        # print(f"Accuracy: {accuracy}")
        # print(f"Accuracy: {sum(accuracy)/len(accuracy)}")
        # print(classification_report(
        #     target.numpy(),
        #     out.numpy(),
        #     digits=4,
        #     output_dict=output_dict,
        #     zero_division=1,))
        return sum(accuracy)/len(accuracy)


def get_predictions(n, X_test, y_test):
    print(f"Making predictions for {len(X_test)} test instances::")
    print("Instance: y,y_pred,y_pred_prob,oth_pred,oth_pred_prob")

    i = 0
    for (x, y) in list(zip(X_test, y_test)):
        n.reset()
        preds = n.forward(x)
        preds.cpu().detach()
        if not torch.sum(preds):
            preds = torch.tensor([1, 0])
        preds = preds / torch.sum(preds)
        y_pred_prob = torch.max(preds)
        y_pred = torch.argmax(preds)
        # compute prob for the other class
        if y_pred:
            oth_pred = 0
        else:
            oth_pred = 1
        oth_pred_prob = 1 - y_pred_prob
        print(
            f"Inst {i}: {y},{y_pred},{y_pred_prob:.6f},{oth_pred},{oth_pred_prob:.6f}"
        )
        i = i + 1


def seed_all(seed: int) -> None:
    """Setup random state from a seed for `torch`, `random` and optionally `numpy` (if can be imported).

    Args:
        seed: Random state seed
    """
    random.seed(seed)
    torch.manual_seed(seed)

    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)

    try:
        import torch_xla.core.xla_model as xm

        xm.set_rng_state(seed)
    except ImportError:
        pass

    try:
        import numpy as np

        np.random.seed(seed)
    except ImportError:
        pass
