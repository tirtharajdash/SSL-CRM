import argparse
import sys

import torch
from torch import nn
import torch.nn.functional as F
from sklearn.model_selection import train_test_split
import matplotlib.pyplot as plt

from crm.core import Network, Decoder_fullyconnected, CRM_model
from crm.utils import (
    get_best_config,
    get_max_explanations,
    get_metrics,
    get_autoencoder_metrics,
    get_predictions,
    load_object,
    make_dataset_cli,
    seed_all,
    train, 
    train_autoencoder,
)


def cmd_line_args():
    parser = argparse.ArgumentParser(
        description="CRM; Example: python3 main.py -f inp.file -o out.file -n 20"
    )
    parser.add_argument("-f", "--file", help="input file", required=True)
    parser.add_argument("-o", "--output", help="output file", required=True)
    parser.add_argument(
        "-s",
        "--saved-model",
        type=str,
        help="location of saved model",
        required=False,
        default=None,
    )
    parser.add_argument(
        "-n", "--num-epochs", type=int, help="number of epochs", required=True
    )
    parser.add_argument(
        "-p", "--predict", help="get predictions for a test set", action="store_true"
    )
    parser.add_argument(
        "-e", "--explain", help="get explanations for predictions", action="store_true"
    )
    parser.add_argument(
        "-t", "--tune", help="tune the hyper parameters", action="store_true"
    )

    parser.add_argument(
        "-v", "--verbose", help="get verbose outputs", action="store_true"
    )
    parser.add_argument("-g", "--gpu", help="run model on gpu", action="store_true")
    args = parser.parse_args()
    return args


class Logger(object):
    def __init__(self, filename):
        self.terminal = sys.stdout
        self.log = open(filename, "a")

    def write(self, message):
        self.terminal.write(message)
        self.log.write(message)

    def flush(self):
        pass


def main():
    seed_all(24)
    torch.set_num_threads(16)
    args = cmd_line_args()
    device = torch.device("cuda" if torch.cuda.is_available() and args.gpu else "cpu")
    sys.stdout = Logger(args.output)
    print(args)

    # Load data
    file_name = args.file
    print("***Loading data***")
    with open(file_name, "r") as f:
        graph_file = f.readline()[:-1]
        train_file = f.readline()[:-1]
        test_files = f.readline()[:-1].split()
        true_explanations = list(map(int, f.readline()[:-1].split()))
        

    X_train, y_train, test_dataset, adj_list, edges = make_dataset_cli(
        graph_file, train_file, test_files, device=device
    )
    
    # Create CRM structure and train with input data
    print("***Creating CRM structure***")
    n = CRM_model(len(adj_list), adj_list, include_top=False, device=device)
    n.to(device)

    # print(f"layers: {n.layers}")
    
    # print(f"layer last: {n.layers[-1].layer_prev.in_features, n.layers[-1].layer_prev.out_features}")
    # quit()
    
    if args.saved_model:
        print("***Loading Saved Model***")
        n = load_object(args.saved_model)


    #criterion = F.cross_entropy
    criterion = F.binary_cross_entropy
    
    optimizer = torch.optim.Adam(n.parameters(), lr=0.001)
    if args.tune:
        print("***Get Best Config***")
        best = get_best_config(
            n, X_train, y_train, args.num_epochs, optimizer, criterion
        )
        print(best)

    print("***Training CRM***")
    X_train, X_val, y_train, y_val = train_test_split(
        X_train, y_train, test_size=0.2, random_state=24, stratify=y_train
    )
    
    #output_shape = len([neuron for neuron in n.neurons if neuron.layer == n.num_layers - 2])    
    decoder_model = Decoder_fullyconnected(n)
    decoder_model.to(device)

    train_losses, train_accs, val_losses, val_accs = train_autoencoder(
    # train_losses, val_losses = train_autoencoder(
        n,
        decoder_model,
        X_train,
        y_train,
        args.num_epochs,
        torch.optim.Adam(n.parameters(), lr=best["lr"] if args.tune else 0.001),
        criterion,
        X_val=X_val,
        y_val=y_val,
        save_here=args.output + "_model",
        verbose=args.verbose,
        device=device,
    )
    
    #define plot_losses function
    def plot_losses(train_losses, val_losses, output):
        plt.plot(train_losses, label="Train Loss")
        if val_losses:
            plt.plot(val_losses, label="Validation Loss")
        plt.xlabel("Epochs")
        plt.ylabel("Loss")
        plt.legend()
        plt.savefig(output)
        plt.close()
    def plot_accs(train_accs, val_accs, output):
        plt.plot(train_accs, label="Train Accuracy")
        if val_accs:
            plt.plot(val_accs, label="Validation Accuracy")
        plt.xlabel("Epochs")
        plt.ylabel("Accuracy")
        plt.legend()
        plt.savefig(output)
        plt.close()
    
    plot_losses(train_losses, val_losses, args.output + "_losses.png")
    plot_accs(train_accs, val_accs, args.output + "_accs.png")

    # Train metrics
    if not args.saved_model:
        print("***Train Metrics***")
        print(get_autoencoder_metrics(n, decoder_model, X_train))
        print("-------------------------------------")

    # Test metrics
    print("***Test Metrics***")
    for X_test, y_test in test_dataset:
        print(get_autoencoder_metrics(n, decoder_model, X_test))
        print("-------------------------------------")

    # # Predict for the test instances
    # if args.predict:
    #     print("***Predicting the class labels for the test set***")
    #     for X_test, y_test in test_dataset:
    #         get_predictions(n, X_test, y_test)

    # # Explain the test instances
    # if args.explain:
    #     print("***Generating explanations for the test set***")
    #     for X_test, y_test in test_dataset:
    #         # get_explanations(
    #         #    n,
    #         #    X_test,
    #         #    y_test,
    #         #    true_explanations=true_explanations,
    #         #    k=1,
    #         #    verbose=args.verbose
    #         # )

    #         # added by T: get max explanations
    #         get_max_explanations(
    #             n,
    #             X_test,
    #             y_test,
    #             true_explanations=true_explanations,
    #             k=1,
    #             verbose=args.verbose,
    #         )
    #         print("-------------------------------------")


if __name__ == "__main__":
    main()
