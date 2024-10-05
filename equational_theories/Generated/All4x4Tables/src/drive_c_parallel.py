import subprocess
import sys
import os
import multiprocessing

# Constants
BATCH_SIZE = 33554432
TOTAL_BATCHES = 128
C_PROGRAM_NAME = "./a.out"  # Update this to your C program's name
MAX_PARALLEL_PROCESSES = 128  # Use all available CPU cores

def run_batch(batch_number):
    start_index = batch_number * BATCH_SIZE
    end_index = start_index + BATCH_SIZE - 1
    command = [C_PROGRAM_NAME, str(start_index), str(end_index)]
    try:
        result = subprocess.run(command, check=True, capture_output=True, text=True)
        print(f"Batch {batch_number + 1}/{TOTAL_BATCHES} completed: tables {start_index} to {end_index}")
        if result.stderr:
            print(f"Errors in batch {batch_number + 1}:", result.stderr, file=sys.stderr)
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error in batch {batch_number + 1}: {e}", file=sys.stderr)
        print("Stdout:", e.stdout)
        print("Stderr:", e.stderr, file=sys.stderr)
        return None

def main():
    if not os.path.exists(C_PROGRAM_NAME):
        print(f"Error: {C_PROGRAM_NAME} not found. Please compile the C program first.", file=sys.stderr)
        sys.exit(1)

    print(f"Starting parallel execution with {MAX_PARALLEL_PROCESSES} processes")

    with multiprocessing.Pool(processes=MAX_PARALLEL_PROCESSES) as pool:
        results = pool.map(run_batch, range(TOTAL_BATCHES))

    # Process and aggregate results
    successful_batches = sum(1 for result in results if result is not None)
    print(f"\nExecution completed. Successful batches: {successful_batches}/{TOTAL_BATCHES}")

if __name__ == "__main__":
    main()
