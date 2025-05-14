import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from sklearn.metrics import confusion_matrix

def confuse(csvfile):
    # Adjust the CSV file name as needed.
    csv_file = csvfile
    df = pd.read_csv(csv_file)
    def parse_bool(val):
        return bool(val)
    
    df["ground_truth"] = df.apply(lambda row: 1 if not parse_bool(row["Original Failed"]) else 0, axis=1)
    df["prediction"]   = df.apply(lambda row: 1 if not parse_bool(row["Mutated Failed"]) else 0, axis=1)

    df["gt"] = df.apply(lambda row: 1 if not parse_bool(row["Original Compiles"]) else 0, axis=1)
    df["p"]   = df.apply(lambda row: 1 if not parse_bool(row["Mutated Compiles"]) else 0, axis=1)
    '''

    # Compute confusion matrix using scikit-learn
    # We define "1" as "Compiled" (i.e. positive outcome) and "0" as "Failed"
    y_true = df["ground_truth"]
    y_pred = df["prediction"]
    cm = confusion_matrix(y_true, y_pred, labels=[1, 0])
    # The ordering here is intentional:
    #   - cm[0,0] = True Positives    (TP): original compiled and mutated compiled
    #   - cm[0,1] = False Negatives   (FN): original compiled but mutated failed
    #   - cm[1,0] = False Positives   (FP): original failed but mutated compiled
    #   - cm[1,1] = True Negatives    (TN): original failed and mutated failed

    # Optional: Plot the confusion matrix using a heatmap for clearer visualization.
    plt.figure(figsize=(6,5))
    sns.heatmap(cm, annot=True, fmt="d", cmap="Blues",
                xticklabels=["LLM Output", "Failed"],
                yticklabels=["LLM Output", "Failed"])
    plt.xlabel("Mutated Prediction")
    plt.ylabel("Original")
    plt.title("Confusion Matrix")
    plt.savefig("CM_LLMOutput.pdf")
    plt.clf()
    '''
    filtered = df[(df["ground_truth"] == 1) & (df["prediction"] == 1)]
    ids = list(set(df["Model"]))

    for model in ids:

        y_true = filtered[(filtered["Model"] == model)]
        y_pred = filtered[(filtered["Model"] == model)]
        y_true = y_true["gt"]
        y_pred = y_pred["p"]
        cm = confusion_matrix(y_true, y_pred, labels=[0,1])

        sns.heatmap(cm, annot=True, fmt="d", cmap="Blues",
                    xticklabels=["Compiles", "Does Not Compile"],
                    yticklabels=["Compiles", "Does Not Compile"])
        plt.xlabel("Mutated")
        plt.ylabel("Original")
        plt.title(f"Coq Code Compiles Model: {model}")
        plt.savefig(f"CM_Compiles_Model_{model}.pdf")
        plt.clf()

confuse("../results.csv")


