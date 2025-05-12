import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from sklearn.metrics import confusion_matrix

def main():
    # Adjust the CSV file name as needed.
    csv_file = "data.csv"
    df = pd.read_csv(csv_file)

    # Option 1: If the CSV columns "Original Compiles" and "Mutated Compiles" 
    # (as well as "Original Failed" and "Mutated Failed") are stored as booleans or numerics
    # where a truthy value indicates compilation, then you can map the ground truth as follows:
    #
    # Ground Truth: 1 (Compiled) if the "Original Compiles" column is True, else 0 (Failed)
    # Hypothesis: 1 (Compiled) if the "Mutated Compiles" column is True, else 0 (Failed)
    
    def parse_bool(val):
        # If your CSV values are strings like "True"/"False", uncomment the next line:
        # return True if str(val).strip().lower() == "true" else False
        return bool(val)

    # Create new columns 'ground_truth' and 'prediction' according to our mapping.
    df["ground_truth"] = df.apply(lambda row: 1 if parse_bool(row["Original Compiles"]) else 0, axis=1)
    df["prediction"]   = df.apply(lambda row: 1 if parse_bool(row["Mutated Compiles"]) else 0, axis=1)

    # Alternatively, you could use the complementary Failed columns to validate your data. 

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

    print("Confusion Matrix (Rows: Ground Truth, Columns: Predictions):")
    print(cm)

    # Alternatively, manually count the confusion matrix components:
    TP = ((y_true == 1) & (y_pred == 1)).sum()
    TN = ((y_true == 0) & (y_pred == 0)).sum()
    FP = ((y_true == 0) & (y_pred == 1)).sum()  # False Positive: Mutated Compiles while Original Failed
    FN = ((y_true == 1) & (y_pred == 0)).sum()  # False Negative: Mutated Fails while Original Compiled

    print(f"True Positives: {TP}")
    print(f"True Negatives: {TN}")
    print(f"False Positives: {FP}")
    print(f"False Negatives: {FN}")

    # Optional: Plot the confusion matrix using a heatmap for clearer visualization.
    plt.figure(figsize=(6,5))
    sns.heatmap(cm, annot=True, fmt="d", cmap="Blues",
                xticklabels=["Compiled", "Failed"],
                yticklabels=["Compiled", "Failed"])
    plt.xlabel("Mutated Prediction")
    plt.ylabel("Original (Ground Truth)")
    plt.title("Confusion Matrix")
    plt.show()

if __name__ == "__main__":
    main()