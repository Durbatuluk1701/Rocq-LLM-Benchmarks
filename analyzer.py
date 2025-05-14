# analytics_script_v2.py
#
# Performs detailed data analysis on 'results.csv', focusing on
# compilation/failure statistics, mismatches, model comparison,
# and stratified reporting.
#
# To use:
# 1. Ensure Python and pandas are installed.
# 2. Save as 'analytics_script_v2.py'.
# 3. Place 'results.csv' in the same directory.
# 4. Run: python analytics_script_v2.py

import pandas as pd

pd.options.display.float_format = "{:,.2f}".format

# Define the columns of interest
COLUMNS_TO_ANALYZE = [
    "Original Compiles",
    "Original Failed",
    "Mutated Compiles",
    "Mutated Failed",
]
MODEL_COLUMN = "Model"
FILE_COLUMN = "File"
THEOREM_NAME_COLUMN = "Orig Theorem Name"


def load_and_preprocess_data(csv_filepath="results.csv"):
    """Loads and preprocesses the CSV data."""
    try:
        df = pd.read_csv(csv_filepath)
    except FileNotFoundError:
        print(
            f"Error: File '{csv_filepath}' not found. Ensure it's in the script's directory."
        )
        return None

    for col in COLUMNS_TO_ANALYZE:
        if col in df.columns:
            df[col] = df[col].fillna("").astype(str).str.strip().str.lower()
            df[col] = (
                df[col]
                .map({"true": True, "false": False, "": False, "nan": False})
                .fillna(False)
            )
            df[col] = df[col].astype(bool)
        else:
            print(
                f"Warning: Analysis column '{col}' not found. Creating it as all False."
            )
            df[col] = False

    if MODEL_COLUMN not in df.columns:
        print(
            f"Warning: '{MODEL_COLUMN}' column not found. Model-specific analyses will be affected."
        )
    if THEOREM_NAME_COLUMN not in df.columns:
        print(
            f"Warning: '{THEOREM_NAME_COLUMN}' column not found. Theorem-specific analyses will be affected."
        )
    if FILE_COLUMN not in df.columns:
        print(
            f"Warning: '{FILE_COLUMN}' column not found. File-specific analyses will be affected."
        )

    return df


def print_overall_statistics(df):
    """Prints basic overall statistics for the key columns."""
    print("\n--- 1. Overall Basic Statistics ---")
    total_entries = len(df)
    if total_entries == 0:
        print("No data to analyze.")
        return
    print(f"Total entries: {total_entries}")
    for col in COLUMNS_TO_ANALYZE:
        count = df[col].sum()
        print(f"Total {col}: {count} ({count/total_entries*100:.2f}%)")


def analyze_compilation_failure_mismatches(df):
    """
    Addresses Points 1 & 2:
    1. How often did a test Compile on Orig+Mut, but not the other.
    2. How often a test fails on Orig+Mut, but not the other.
    """
    print("\n--- 2. Compilation and Failure Mismatches (Original vs. Mutated) ---")
    total_entries = len(df)
    if total_entries == 0:
        return

    # Point 1: Compilation Mismatches
    orig_comp_not_mut_comp = df[
        df["Original Compiles"] & ~df["Mutated Compiles"]
    ].shape[0]
    mut_comp_not_orig_comp = df[
        ~df["Original Compiles"] & df["Mutated Compiles"]
    ].shape[0]
    print("Compilation Mismatches:")
    print(
        f"  - Original Compiled AND Mutated Did NOT Compile: {orig_comp_not_mut_comp} ({orig_comp_not_mut_comp/total_entries*100:.2f}%)"
    )
    print(
        f"  - Original Did NOT Compile AND Mutated Compiled: {mut_comp_not_orig_comp} ({mut_comp_not_orig_comp/total_entries*100:.2f}%)"
    )

    # Point 2: Failure Mismatches
    orig_fail_not_mut_fail = df[df["Original Failed"] & ~df["Mutated Failed"]].shape[0]
    mut_fail_not_orig_fail = df[~df["Original Failed"] & df["Mutated Failed"]].shape[0]
    print("\nFailure Mismatches:")
    print(
        f"  - Original Failed AND Mutated Did NOT Fail: {orig_fail_not_mut_fail} ({orig_fail_not_mut_fail/total_entries*100:.2f}%)"
    )
    print(
        f"  - Original Did NOT Fail AND Mutated Failed: {mut_fail_not_orig_fail} ({mut_fail_not_orig_fail/total_entries*100:.2f}%)"
    )


def analyze_comp_mismatches_no_failures(df):
    """
    Addresses Point 3: Point 1 stats if we remove any cases where EITHER failed.
    (Interpreted as: Original Failed is False AND Mutated Failed is False)
    """
    print("\n--- 3. Compilation Mismatches (Excluding Any Failures) ---")

    # Filter out rows where any failure occurred
    df_no_failures = df[~df["Original Failed"] & ~df["Mutated Failed"]]
    total_entries_no_failures = len(df_no_failures)

    if total_entries_no_failures == 0:
        print("No entries left after filtering out all failures.")
        return

    print(
        f"Entries considered (Original Failed=False AND Mutated Failed=False): {total_entries_no_failures}"
    )

    orig_comp_not_mut_comp = df_no_failures[
        df_no_failures["Original Compiles"] & ~df_no_failures["Mutated Compiles"]
    ].shape[0]
    mut_comp_not_orig_comp = df_no_failures[
        ~df_no_failures["Original Compiles"] & df_no_failures["Mutated Compiles"]
    ].shape[0]

    print("Compilation Mismatches (in this no-failure subset):")
    print(
        f"  - Original Compiled AND Mutated Did NOT Compile: {orig_comp_not_mut_comp} ({orig_comp_not_mut_comp/total_entries_no_failures*100:.2f}%)"
    )
    print(
        f"  - Original Did NOT Compile AND Mutated Compiled: {mut_comp_not_orig_comp} ({mut_comp_not_orig_comp/total_entries_no_failures*100:.2f}%)"
    )


def analyze_comp_mismatches_no_failures_model_specific(df):
    """
    Addresses Point 3: Point 1 stats if we remove any cases where EITHER failed.
    (Interpreted as: Original Failed is False AND Mutated Failed is False)
    """
    print("\n--- 3.1. Compilation Mismatches (Excluding Any Failures) ---")

    # Filter out rows where any failure occurred
    df_no_failures = df[~df["Original Failed"] & ~df["Mutated Failed"]]
    total_entries_no_failures = len(df_no_failures)

    if total_entries_no_failures == 0:
        print("No entries left after filtering out all failures.")
        return

    print(
        f"Entries considered (Original Failed=False AND Mutated Failed=False): {total_entries_no_failures}"
    )

    MODEL_KEYS = ["llama3.1", "phi4"]

    print("-" * 20)
    for model in MODEL_KEYS:
        print("-" * 20)
        print(f"\nModel: {model}")
        orig_comp_not_mut_comp = df_no_failures[
            (df_no_failures["Model"] == model)
            & df_no_failures["Original Compiles"]
            & ~df_no_failures["Mutated Compiles"]
        ].shape[0]
        mut_comp_not_orig_comp = df_no_failures[
            (df_no_failures["Model"] == model)
            & ~df_no_failures["Original Compiles"]
            & df_no_failures["Mutated Compiles"]
        ].shape[0]

        print("Compilation Mismatches (in this no-failure subset):")
        print(
            f"  - Original Compiled AND Mutated Did NOT Compile: {orig_comp_not_mut_comp} ({orig_comp_not_mut_comp/total_entries_no_failures*100:.2f}%)"
        )
        print(
            f"  - Original Did NOT Compile AND Mutated Compiled: {mut_comp_not_orig_comp} ({mut_comp_not_orig_comp/total_entries_no_failures*100:.2f}%)"
        )
        print("-" * 20)

    print("-" * 20)


def determine_best_model(df):
    """
    Addresses Point 4: Which model performed best overall.
    Prints key performance indicators per model for comparison.
    """
    print("\n--- 4. Model Performance Comparison ---")
    if MODEL_COLUMN not in df.columns or df[MODEL_COLUMN].isnull().all():
        print(
            f"Cannot determine best model as '{MODEL_COLUMN}' column is missing or empty."
        )
        return

    models_summary = []
    for model_name, model_df in df.groupby(MODEL_COLUMN):
        total_model_entries = len(model_df)
        if total_model_entries == 0:
            continue

        summary = {"Model": model_name, "Entries": total_model_entries}
        for col in COLUMNS_TO_ANALYZE:
            count = model_df[col].sum()
            summary[f"{col} (%)"] = (count / total_model_entries) * 100
            summary[f"{col} (Count)"] = count

        # Specific "Killed" and "Fixed" metrics for context
        # summary["Killed (OrigC & MutF) (%)"] = (
        #     model_df[model_df["Original Compiles"] & model_df["Mutated Failed"]].shape[
        #         0
        #     ]
        #     / total_model_entries
        # ) * 100
        # summary["Fixed (OrigF & MutC) (%)"] = (
        #     model_df[model_df["Original Failed"] & model_df["Mutated Compiles"]].shape[
        #         0
        #     ]
        #     / total_model_entries
        # ) * 100

        models_summary.append(summary)

        df_no_failures = model_df[
            ~model_df["Original Failed"] & ~model_df["Mutated Failed"]
        ]
        total_model_entries = len(df_no_failures)
        if total_model_entries == 0:
            continue

        summary = {
            "Model": model_name + "(no failures)",
            "Entries": total_model_entries,
        }
        for col in COLUMNS_TO_ANALYZE:
            count = df_no_failures[col].sum()
            summary[f"{col} (%)"] = (count / total_model_entries) * 100
            summary[f"{col} (Count)"] = count

        models_summary.append(summary)

    if not models_summary:
        print("No model data to summarize.")
        return

    summary_df = pd.DataFrame(models_summary)
    print(
        "Key Performance Indicators by Model (Percentages unless specified as Count):"
    )

    # Define a preferred order of columns for display
    cols_ordered = [
        "Model",
        "Entries",
        "Original Compiles (%)",
        "Mutated Compiles (%)",
        "Original Failed (%)",
        "Mutated Failed (%)",
        "Killed (OrigC & MutF) (%)",
        "Fixed (OrigF & MutC) (%)",
        "Original Compiles (Count)",
        "Mutated Compiles (Count)",
        "Original Failed (Count)",
        "Mutated Failed (Count)",
    ]
    # Filter for columns that actually exist in summary_df to avoid KeyErrors
    cols_to_print = [col for col in cols_ordered if col in summary_df.columns]

    print(summary_df[cols_to_print].to_string(index=False))

    print("\nInterpretation of 'Best Model':")
    print(
        "- Higher 'Original Compiles (%)' and 'Mutated Compiles (%)' are generally better."
    )
    print(
        "- Lower 'Original Failed (%)' and 'Mutated Failed (%)' are generally better."
    )
    print("- Lower 'Killed (%)' is critical (shows robustness to mutation).")
    print(
        "- Higher 'Fixed (%)' might indicate the model's ability to correct initially problematic mutations or handle tricky original failures, but interpretation depends on context."
    )


def cross_model_theorem_performance(df):
    """
    Addresses Point 5: Cases where a specific theorem (by "Orig Theorem Name")
    succeeded (Original Compiles=True) for one model, but not for another.
    "Not succeeded" is interpreted as Original Compiles=False.
    """
    print(
        "\n--- 5. Cross-Model Theorem Compilation Discrepancies (Original Theorems) ---"
    )
    if (
        THEOREM_NAME_COLUMN not in df.columns
        or df[THEOREM_NAME_COLUMN].isnull().all()
        or MODEL_COLUMN not in df.columns
        or df[MODEL_COLUMN].isnull().all()
    ):
        print(
            f"Cannot perform cross-model theorem analysis due to missing '{THEOREM_NAME_COLUMN}' or '{MODEL_COLUMN}' data."
        )
        return

    # Consider only unique theorem-model original compilation results
    # If a theorem appears multiple times for the same model, this takes the first.
    # A more robust approach might be df.groupby([THEOREM_NAME_COLUMN, MODEL_COLUMN])["Original Compiles"].any() or .all()
    # For simplicity, we assume each entry is a distinct test run, or we pivot directly.

    try:
        pivot_df = df.pivot_table(
            index=THEOREM_NAME_COLUMN,
            columns=MODEL_COLUMN,
            values="Original Compiles",
            aggfunc="any",  # Use 'any' if multiple entries per theorem-model exist, True if any compiled
        )
    except Exception as e:
        print(f"Could not create pivot table for cross-model analysis: {e}")
        print(
            "This might happen if there are duplicate (Theorem, Model) entries that pandas cannot aggregate by default with pivot_table without an aggfunc, or other data issues."
        )
        print("Using a groupby approach instead for a summary:")

        discrepancy_count_summary = 0
        unique_theorems = df[THEOREM_NAME_COLUMN].dropna().unique()
        for theorem_name in unique_theorems:
            theorem_df = df[df[THEOREM_NAME_COLUMN] == theorem_name]
            model_comp_status = theorem_df.groupby(MODEL_COLUMN)[
                "Original Compiles"
            ].any()  # True if any entry for that model compiled

            compiled_models = set(model_comp_status[model_comp_status == True].index)
            not_compiled_models = set(
                model_comp_status[model_comp_status == False].index
            )

            if (
                compiled_models and not_compiled_models
            ):  # Theorem compiled on some models but not others
                discrepancy_count_summary += 1
        print(
            f"  Number of theorems that compiled on at least one model but not on at least one other model: {discrepancy_count_summary}"
        )
        return

    if pivot_df.empty:
        print("Pivot table for cross-model analysis is empty.")
        return

    models = pivot_df.columns
    if len(models) < 2:
        print("Need at least two models to compare for discrepancies.")
        return

    discrepancy_count = 0
    detailed_discrepancies = []

    for theorem_name, row in pivot_df.iterrows():
        compiled_on = [model for model in models if pd.notna(row[model]) and row[model]]
        not_compiled_on = [
            model for model in models if pd.notna(row[model]) and not row[model]
        ]  # Or pd.isna(row[model]) if that means "did not compile"

        # Check for NaN specifically if it should be treated as "did not compile"
        # For simplicity, assuming row[model] being False covers "did not compile". NaN might mean "not tested".
        # This logic counts if a theorem compiled on SOME models and did NOT compile on OTHERS.
        if compiled_on and not_compiled_on:
            discrepancy_count += 1
            # detailed_discrepancies.append(f"  - Theorem '{theorem_name}': Compiled on {compiled_on}, Did NOT compile on {not_compiled_on}")

    print(
        f"Total theorems with compilation discrepancies (Original Compiles status differs across models): {discrepancy_count}"
    )
    # if detailed_discrepancies:
    #     print("Examples of discrepancies (first 5):")
    #     for entry in detailed_discrepancies[:5]:
    #         print(entry)
    # else:
    #     print("No theorems found where 'Original Compiles' status differed across models.")


def statistics_by_generic_group(df, group_column, group_name_singular):
    """
    Addresses Point 6: Stratified stats by a generic group (File, Theorem).
    """
    print(f"\n--- 6. Statistics Stratified by {group_name_singular} ---")
    if group_column not in df.columns or df[group_column].isnull().all():
        print(
            f"Cannot stratify by '{group_name_singular}' as column '{group_column}' is missing or empty."
        )
        return

    # For 'Orig Theorem Name', output can be long. Consider summarizing.
    # For now, print stats for each group.

    grouped_data = df.groupby(group_column)

    print(f"Total unique {group_name_singular}s: {len(grouped_data)}")

    # Limiting output for very numerous groups like individual theorems
    # Outputting full stats for groups with few members (e.g. Files)
    # Outputting summary for groups with many members (e.g. Theorems)

    if (
        len(grouped_data) > 20 and group_column == THEOREM_NAME_COLUMN
    ):  # Heuristic for 'Orig Theorem Name'
        print(
            f"Summarizing for '{group_name_singular}' due to large number of groups..."
        )

        # Example summary: How many theorems compiled on N models (assuming entries are per model per theorem)
        # This part needs careful thought if 'Model' column is not consistently populated per theorem.
        # Let's provide a summary of compilation rates for theorems.
        theorem_summary = []
        for name, group in grouped_data:
            total_entries = len(group)
            if total_entries == 0:
                continue
            oc_rate = group["Original Compiles"].sum() / total_entries * 100
            mc_rate = group["Mutated Compiles"].sum() / total_entries * 100
            theorem_summary.append(
                {
                    group_name_singular: name,
                    "Entries": total_entries,
                    "Avg Orig. Compiles (%)": oc_rate,
                    "Avg Mut. Compiles (%)": mc_rate,
                    "Total Orig. Failed": group["Original Failed"].sum(),
                    "Total Mut. Failed": group["Mutated Failed"].sum(),
                }
            )
        summary_df = pd.DataFrame(theorem_summary)
        print("Top 5 theorems by average Original Compilation Rate:")
        print(summary_df.nlargest(5, "Avg Orig. Compiles (%)").to_string(index=False))
        print("\nBottom 5 theorems by average Original Compilation Rate (min 1 entry):")
        print(
            summary_df[summary_df["Entries"] > 0]
            .nsmallest(5, "Avg Orig. Compiles (%)")  # type: ignore (idk why this is just not a valid error!)
            .to_string(index=False)
        )

    else:  # For Files, or if theorems are few
        for name, group in grouped_data:
            print(f"\n{group_name_singular}: {name}")
            total_entries_group = len(group)
            print(
                f"  Total entries for this {group_name_singular}: {total_entries_group}"
            )
            for col in COLUMNS_TO_ANALYZE:
                count = group[col].sum()
                percentage = (
                    (count / total_entries_group) * 100
                    if total_entries_group > 0
                    else 0
                )
                print(f"  Total {col}: {count} ({percentage:.2f}%)")
            # Basic transition for context if needed
            killed = group[group["Original Compiles"] & group["Mutated Failed"]].shape[
                0
            ]
            fixed = group[group["Original Failed"] & group["Mutated Compiles"]].shape[0]
            print(
                f"  'Killed' (OrigC & MutF): {killed} ({(killed/total_entries_group)*100:.2f}%)"
            )
            print(
                f"  'Fixed' (OrigF & MutC): {fixed} ({(fixed/total_entries_group)*100:.2f}%)"
            )


def main_analysis_flow():
    print("Starting detailed data analysis for 'results.csv'...")
    df = load_and_preprocess_data()

    if df is None or df.empty:
        print("Data loading failed or produced an empty DataFrame. Aborting analysis.")
        return

    # Point 1 (Implicitly covered by Overall Basic Statistics)
    print_overall_statistics(df)  # General overview

    # Point 1 & 2 (Specific Mismatches)
    analyze_compilation_failure_mismatches(df)

    # Point 3
    analyze_comp_mismatches_no_failures(df)
    # point 3.1
    analyze_comp_mismatches_no_failures_model_specific(df)

    # Point 4
    determine_best_model(df)

    # Point 5
    cross_model_theorem_performance(df)

    # Point 6: Stratified statistics (Model is covered by determine_best_model / or a dedicated function similar to prior script)
    # Previous script's statistics_by_model provides this, can be called or integrated
    # For this version, `determine_best_model` gives a good summary per model.
    # Adding stratification by File and Theorem Name
    if FILE_COLUMN in df.columns:
        statistics_by_generic_group(df, FILE_COLUMN, "File")
    if THEOREM_NAME_COLUMN in df.columns:
        statistics_by_generic_group(df, THEOREM_NAME_COLUMN, "Orig Theorem Name")

    # Original transition analysis (from previous script) can be useful too
    # transition_analysis(df) # For overall transitions
    # statistics_by_model(df) # For per-model transitions, if more detail than `determine_best_model` is needed

    print("\nDetailed analysis complete.")


if __name__ == "__main__":
    main_analysis_flow()
