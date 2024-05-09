import os
import argparse
import typing as typ
from enum import Enum
from typing import List

class EndToEndKind(Enum):
    full = 1
    ast_and_full_cfg = 2
    only_full_cfg = 3

class TestData(typ.NamedTuple):
    file: str
    num_procedures: int
    isabelle_loc: int
    end_to_end_proof: List[EndToEndKind] 
    # for each procedure proof provides end-to-end proof kind (i.e., length should match num_procedures)

def file_exists_in_dir(file, path) -> bool:
    return file in os.listdir(path)

def check_string_exists_in_file(search_string, path) -> bool:
    if not(os.path.isfile(path)):
        print("ERROR: {} is not an existing file.".format(path))
        exit(1)

    matches = [line for line in open(path,'r') if search_string in line]
    return matches != []


def ast_to_cfg_proof(dir, procedure_name):
    return os.path.join(dir, procedure_name+"_asttocfg_proof.thy")

def cfg_opt_proof(dir, procedure_name):
    return os.path.join(dir, procedure_name+"_cfgoptimizations_proof.thy")

def cfg_to_dag_proof(dir, procedure_name):
    return os.path.join(dir, procedure_name+"_cfgtodag_proof.thy")

def get_e2e_kind(procedure_name, dir) -> EndToEndKind:
    ast_exists : bool = os.path.isfile(ast_to_cfg_proof(dir, procedure_name))
    if not(os.path.isfile(cfg_to_dag_proof(dir, procedure_name))):
        print("ERROR: CFG-to-DAG proof {} does not exist in {}".format(cfg_to_dag_proof(dir, procedure_name), dir))
        exit(1)

    # important to query cfg_to_dag first, since cfg_opt proof may not exist (relies on lazy evaluation of `or`)
    # this is a method because if ast e2e exists then we do not need to evaluate this expression (+ want reuse)
    def cfg_end_to_end():
        return (check_string_exists_in_file("lemma end_to_end_theorem:", cfg_to_dag_proof(dir, procedure_name)) or 
        check_string_exists_in_file("lemma end_to_end_theorem:", cfg_opt_proof(dir, procedure_name)))

    if ast_exists:
        if check_string_exists_in_file("lemma end_to_end_theorem_ast:", ast_to_cfg_proof(dir, procedure_name)):
            return EndToEndKind.full

        if cfg_end_to_end():
           return EndToEndKind.ast_and_full_cfg
        
        print("ERROR: no end-to-end theorem found in {}".format(dir))
        exit(1)
    
    if cfg_end_to_end():
        return EndToEndKind.only_full_cfg

    print("ERROR: no end-to-end theorem found in {}".format(dir))
    exit(1)

def certificate_size(proof_dir_path) -> int:
    length_certificate = 0
    for root, dirs, files in os.walk(proof_dir_path):        
        for file in files:
            if file.endswith('.thy'):
                file_path = os.path.join(os.path.join(proof_dir_path, root), file)
                file_content = open(file_path, "r")
                nonempty_lines = [line for line in file_content if line.strip() != "\n"]
                length_certificate += len(nonempty_lines)
    
    return length_certificate

def collect_data_single_boogie_file(proof_dir_path, num_procedures):
    e2e_proof_kinds = []
    for procedure_proof in os.listdir(proof_dir_path):
        procedure_proof_path = os.path.join(proof_dir_path, procedure_proof)
        if(os.path.isdir(procedure_proof_path)):
            if(not(procedure_proof.endswith("_proofs"))):
                print("ERROR: procedure proof directory {} does not end with '_proofs'".format(procedure_proof_path))
                exit(1)
            
            procedure_name = procedure_proof.split("_proofs")[0]
            e2e_proof_kind = get_e2e_kind(procedure_name, procedure_proof_path)
            e2e_proof_kinds.append(e2e_proof_kind)
    
    if len(e2e_proof_kinds) != num_procedures:
        print("ERROR: mismatch number of procedures and e2e proofs in {}".format(proof_dir_path))
        exit(1)

    return TestData(file=os.path.basename(proof_dir_path), num_procedures=num_procedures, isabelle_loc=certificate_size(proof_dir_path),end_to_end_proof=e2e_proof_kinds)

def collect_complete_data(boogie_files_dir, boogie_proofs_dir) -> List[TestData]:
    data = []
    boogie_proofs_dir_abs = os.path.abspath(boogie_proofs_dir)
    for proof_dir in os.listdir(boogie_proofs_dir_abs):
        proof_dir_path = os.path.join(boogie_proofs_dir_abs, proof_dir)
        if not(os.path.isfile(os.path.join(proof_dir_path, "ROOT"))):
            print("Skipping {}".format(proof_dir_path))
            continue
        
        if not(proof_dir.endswith("_proofs")):
            print("ERROR: {} does not end with '_proofs'".format(proof_dir))
            exit(1)
            
        boogie_file_name = proof_dir.split("_proofs")[0]+".bpl"
        boogie_file_path = os.path.join(boogie_files_dir, boogie_file_name)
        if not(os.path.isfile(boogie_file_path)):
            print("ERROR: Boogie file {} does not exist".format(boogie_file_path))
            exit(1)

        boogie_file_content = [line for line in open(boogie_file_path,'r')]
        num_procedures = len([line for line in boogie_file_content if line.strip(" ").startswith("procedure ")])

        if num_procedures != len([y for y in os.listdir(proof_dir_path) if os.path.isdir(os.path.join(proof_dir_path, y))]):
            print("ERROR: Number of procedures and number of proofs do not match for {}".format(proof_dir_path))
            exit(1)
        
        data.append(collect_data_single_boogie_file(proof_dir_path, num_procedures))

    return data
            

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-t", "--testsdir",        
        help="Directory where the Boogie files are located, for which the proofs were generated.",
        required=True)

    parser.add_argument(
        "-p", "--proofsdir",        
        help="Directory where the Boogie proofs are located.",
        required=True)


    args = parser.parse_args()

    if (not(os.path.isdir(args.testsdir))):
        print("The input directory " + args.testsdir+ " does not point to an existing directory.")
        exit(1)

    if (not(os.path.isdir(args.proofsdir))):
        print("The input directory " + args.proofsdir+ " does not point to an existing directory.")
        exit(1)

    data : List[TestData] = collect_complete_data(boogie_files_dir=args.testsdir, boogie_proofs_dir=args.proofsdir)

    def count_e2e_kind(kind):
        return sum([len([k for k in d.end_to_end_proof if k == kind]) for d in data])

    num_full_proofs = count_e2e_kind(EndToEndKind.full)
    num_ast_and_full_cfgproofs = count_e2e_kind(EndToEndKind.ast_and_full_cfg)
    num_only_cfg_proofs = count_e2e_kind(EndToEndKind.only_full_cfg)

    print("Full proofs: {}, AST and full CFG proofs: {}, Only CFG proofs: {}".format(
        num_full_proofs,
        num_ast_and_full_cfgproofs,
        num_only_cfg_proofs
    ))

    total_num_procedures = sum([d.num_procedures for d in data])

    if((num_full_proofs + num_ast_and_full_cfgproofs + num_only_cfg_proofs) != total_num_procedures):
        print("ERROR: sum of E2E kinds does not match with length of data")
        exit(1)
    


if __name__ == '__main__':
    main()