import os
import subprocess
import time
import sys
import argparse
import re

boogie_proofgen_bin = 'boogieproof'
boogie_orig_bin = 'boogieorig'

def adjust_and_filter(filename, output_filename):
    n_supported_success = 0
    n_supported_error = 0
    n_empty_files = 0

    with open(output_filename, 'w') as output_file:
        with open(filename) as f:
            print("Starting next selection: Remove all attributes of files in first selection and check if they verify.")
            content = f.readlines()
            for line in content:
                boogie_file = line.rstrip()
                
                newStr = ""
                replaceFile = False
                include = True        
                with open(boogie_file) as f_other:
                    fileContent = f_other.read()
                    
                    #do not include files without any procedures
                    if (not ("procedure" in fileContent)):
                        n_empty_files += 1
                        include = False                      
                    else:
                        # remove attributes
                        if '{:' in fileContent:
                            newStr = re.sub('\{:.["a-zA-Z0-9_$#\.\+\(\) ]*\}','',fileContent)
                            replaceFile = True                            

                # store version without attributes
                if replaceFile and newStr != "":
                    with open(boogie_file, "w") as fout:
                        fout.write(newStr)
                
                if include:
                    # check whether Boogie can verify file with default options (we use the original Boogie version for this)            
                    output = subprocess.check_output([boogie_orig_bin,boogie_file])
                                
                    # space before 0, otherwise "10 errors" would succeed the test as well
                    if " 0 errors" in str(output) and (not ("inconclusive" in str(output))):    
                        n_supported_success += 1
                        print("Selected " + boogie_file)
                        output_file.write(boogie_file+"\n")
                    else:
                        n_supported_error += 1
                        # print("Failure:" + boogie_file)
                

        print("Found " + str(n_supported_success) + " potentially supported tests that are verified after removing all attributes.")
        # print("Found " + str(n_supported_error) + " tests that do not verify")
        # print("Found " + str(n_empty_files) + " tests without any procedures")

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-t", "--testdir",        
        help="Specify test directory containing the Boogie tests.",        
        required=True)

    parser.add_argument(
        "-o", "--outputfile",        
        help="Specify output file containing the list of test that are verified by Boogie and that are (potentially) supported by proof generation.",        
        required=True)

    args = parser.parse_args()

    if(not(os.path.isdir(args.testdir))):
        print(args.testdir + " is not a directory.")
        exit(1)

    if(os.path.exists(args.outputfile)):
        print(args.outputfile + " already exists.")
        exit(1)
    
    # write all Boogie test file paths that are potentially supported by proof generation into a temporary file 
    filename = time.strftime("%Y%m%d-%H%M%S")+"_potentially_supported.log"
    with open(filename, 'w') as potentially_supported_file:
        print("Starting coarse-grained selection of tests")
        n_candidate_files = 0
        for root, dirs, files in os.walk(args.testdir):
            for file in files:
                if file.endswith('.bpl'):
                    test_file_path = os.path.join(root, file)

                    with open(test_file_path) as f:
                        n_candidate_files += 1                    
                        output = subprocess.check_output([boogie_proofgen_bin, "/onlyCheckProofGenSupport",test_file_path]).decode(sys.stdout.encoding)
                        #potentially_supported_file.write(out)
                        output_split = output.splitlines()
                        if len(output_split) > 0 and output_split[0].startswith("Success:"):
                            # print(output_split[0][8:])
                            potentially_supported_file.write(output_split[0][8:]+"\n")
        print("Finished coarse-grained selection of tests")
    
    """ 
     From the identified files, select those tests that verify after removing attributes 
     (this has a side effect on the files --> attributes removed).
    """
    adjust_and_filter(filename, args.outputfile)

    # remove the temporary file
    os.remove(filename)


if __name__ == '__main__':
    main()