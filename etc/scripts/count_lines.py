import os
import argparse

def print_theory_line_info(input_folder):
    for dir in os.listdir(input_folder):
        dir_path = os.path.join(input_folder, dir)
        length_certificate = 0
        has_theories = False
        for root, dirs, files in os.walk(dir_path):        
            for file in files:
                if file.endswith('.thy'):
                    has_theories = True
                    file_path = os.path.join(os.path.join(dir_path, root), file)
                    file_content = open(file_path, "r")
                    nonempty_lines = [line.strip("\n") for line in file_content if line != "\n"]
                    length_certificate += len(nonempty_lines)
        
        if has_theories:
            print("Non-empty lines for " + dir_path + ": " + str(length_certificate))

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-i", "--inputdir",        
        help="Directory where all Boogie files are located, for which proofs should be generated.",
        required=True)

    args = parser.parse_args()

    if (not(os.path.isdir(args.inputdir))):
        print("The input directory " + args.inputdir + " does not point to an existing directory.")
        exit(1)

    print_theory_line_info(args.inputdir)

if __name__ == '__main__':
    main()