import os
import subprocess
import argparse

def generate_proofs(input_dir, output_dir, boogie_proofgen_bin):
    n_success = 0
    n_failure = 0
    n_ignored = 0

    # turn input directory path into an absolute path, since we are going to 
    # change the working directory
    input_dir_absolute = os.path.abspath(input_dir)    

    os.mkdir(output_dir)
    os.chdir(output_dir)

    for root, dirs, files in os.walk(input_dir_absolute):
        for file in files:
            if file.endswith('.bpl'):
                boogie_file_path = os.path.join(root, file)

                with open(boogie_file_path) as f:
                    first_line = f.readline().strip('\n')
                    if(first_line != "//:: ProofGen(IgnoreFile)"):
                        # check whether Boogie can produce certificates
                        errorcode = subprocess.run([boogie_proofgen_bin, boogie_file_path],stdout=subprocess.DEVNULL)
                        if(errorcode.returncode == 0):
                            print("Generated proofs for: " + boogie_file_path)
                            n_success += 1
                        else:
                            print("Could not generate proofs for: " + boogie_file_path)
                            n_failure += 1
                            exit(1)
                    else:
                        #ignore file
                        print("Ignored :" + boogie_file_path)
                        n_ignored += 1
                        pass
                    
    print("Generated proofs for " + str(n_success) + " tests")
    print("Could not generate proofs for " + str(n_failure) + " tests")
    print("Ignored " + str(n_ignored) + " tests")

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-i", "--inputdir",        
        help="Directory where all Boogie files are located, for which proofs should be generated.",
        required=True)

    parser.add_argument(
        "-o", "--outputdir",
        help="Directory in which the proofs should be stored. The directory should not exist yet.",
        required=True
    )

    parser.add_argument(
        "-b", "--boogieproofExe",
        help="Path to Boogie proof generation executable (must be an absolute path or a command that can be executed from any directory)",
        default="boogieproof"
    )

    args = parser.parse_args()

    if (not(os.path.isdir(args.inputdir))):
        print("The input directory " + args.inputdir + " does not point to an existing directory.")
        exit(1)
    
    if (os.path.exists(args.outputdir)):
        print("The desired path " +  args.outputdir + " for the output directory already exists")
        exit(1)
    
    generate_proofs(args.inputdir, args.outputdir, args.boogieproofExe)

if __name__ == '__main__':
    main()