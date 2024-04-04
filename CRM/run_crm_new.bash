#!/bin/bash

# List of dataset names
# datasets=("gi50_screen_A498"
# "gi50_screen_A549_ATCC"
# "gi50_screen_ACHN"
# "gi50_screen_BT_549"
# "gi50_screen_CAKI_1"
# "gi50_screen_CCRF_CEM"
# "gi50_screen_COLO_205"
# "gi50_screen_DLD_1"
# "gi50_screen_DMS_114"
# "gi50_screen_786_0")
datasets=("gi50_screen_A498")


# Iterate through the dataset names
for dataset in "${datasets[@]}"
do
    echo $dataset
    #rm crm_structure.pl train_pos train_neg test_pos test_neg
    #datadir="./data/NCI-datasets-repeats/$dataset"
    datadir="./data/new-datasets/output/$dataset"

    fileprefix="simple_d3"
    ln -s ./lcrm_10_10_simple_d3.pl crm_structure.pl
    ln -s $datadir/crm/simple_d3/$fileprefix\_train_features_pos train_pos
    ln -s $datadir/crm/simple_d3/$fileprefix\_train_features_neg train_neg
    ln -s $datadir/crm/simple_d3/$fileprefix\_test_features_pos test_pos
    ln -s $datadir/crm/simple_d3/$fileprefix\_test_features_neg test_neg

    python3 main2.py -f ./repeat-config  -o ./demo_new -n 1 -g

    #wc -l crm_structure.pl train_pos train_neg test_pos test_neg
    rm crm_structure.pl train_pos train_neg test_pos test_neg
    
done