import os
import subprocess
import time
import statistics as stat
import csv
import argparse

def append_results_to_file(file, times, csv_writer):
    row = [file,stat.mean(times), stat.median(times), stat.pstdev(times)]
    csv_writer.writerow(row)

def check_proofs(input_folder, n_reps):
    full_start_time = time.time()

    timestr = time.strftime("%Y%m%d_%H%M%S")
    output_file_name = timestr+"_"+"timing_certificates.csv" 
    with open(os.path.join(input_folder, output_file_name), 'w', newline='') as output_file:
        writer = csv.writer(output_file, delimiter=',')
        writer.writerow(["File","Mean","Median","Pstdev."])

        n_success = 0
        n_failure = 0
        for root, dirs, files in os.walk(input_folder):
            for dir in dirs:
                root_session_file = os.path.join(root, os.path.join(dir, "ROOT"))
                if(os.path.isfile(root_session_file)):

                    # build session
                    print("Checking " + dir)
                    root_dir = os.path.join(root, dir)                    
                    times = []
                    
                    for i in range(0,n_reps):
                        start_time = time.time()

                        """
                        Isabelle options:
                         * -j4 uses up to 4 cores
                         * -c cleans previous builds of the same session (otherwise the proofs may not be re-checked)
                         * `-D root_dir` states that all Isabelle sessions in `root_dir` should be built
                        """
                        error_code = subprocess.run(["isabelle", "build", "-j4", "-c", "-D", root_dir], stdout=subprocess.DEVNULL)
                        duration = time.time() - start_time
                        times.append(duration)
                    
                    append_results_to_file(root_session_file, times, writer)

                    # assume isabelle is deterministic (i.e., sufficient to just check final return code)
                    if error_code.returncode == 0:
                        n_success += 1
                        print("Success")
                    else:
                        n_failure += 1
                        print("Failure")

        full_duration = time.time() - full_start_time
        print("Finished in " + str(full_duration) + " seconds")
        print("Succeeded: " + str(n_success))
        print("Failed: " + str(n_failure))

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-d", "--inputdir",        
        help="Specify input directory containing the generated proofs.",        
        required=True)

    parser.add_argument(
        "-r", "--reps",
        help="Specify the number of times the same proof should be checked (for timing purposes).",
        type=int,
        default=1)

    args = parser.parse_args()

    if args.reps <= 0:
        print("Number of repetitions has to be at least 1.")
        exit(1)

    check_proofs(args.inputdir, args.reps)

if __name__ == '__main__':
    main()