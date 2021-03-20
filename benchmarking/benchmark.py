import matplotlib.pyplot as plt
import pandas as pd
import numpy as np
import os, fileinput
from shutil import copyfile
import json

def get_config():
    # default values
    cwd = os.getcwd()
    with open(f'./config.json', 'r') as f:
        conf = json.load(f)

    conf["cwd"] = cwd

    # Ask user if tool should compile inputs
    while True:
        cmpl = input(f"[{'y' if conf['compile'] else 'n'}] Compile? (y/n)")
        cmpl_low = cmpl.lower()
        if cmpl_low == "y":
            print("Compiling")
            conf["compile"] = True
            break
        elif cmpl_low == "n":
            print("Not compiling")
            conf["compile"] = False
            break
    
    # Ask user if tool should benchmark
    while True:
        benchmark = input(f"[{'y' if conf['benchmark'] else 'n'}] Benchmark? (y/n)")
        benchmark_low = benchmark.lower()
        if benchmark_low == "y":
            print("Benchmarking")
            conf["benchmark"] = True
            break
        elif benchmark_low == "n":
            print("Not Benchmarking")
            conf["benchmark"] = False
            break    

    print(json.dumps(conf))

    return conf

def setup(conf):
    # For each file in the input directory add a copy of the file 
    # with all wildcard statements replaced by sWildcard ones
    intermediateDirPath = f"{conf['cwd']}/intermediate"
    try:
        if not os.path.exists(intermediateDirPath):
            os.mkdir(intermediateDirPath)
    except OSError:
        print("Creation of intermediate directory failed")

    for entry in os.scandir(f'{conf["cwd"]}/{conf["input_dir"]}'):
        input_file_name = os.path.basename(entry.path).split('.')[0]
        if (entry.path.endswith(".vpr") and not entry.path.endswith("sWildcard.vpr")) and entry.is_file():
            tmp_path = f"{intermediateDirPath}/{input_file_name}"
            try:
                if not os.path.exists(tmp_path):
                    os.mkdir(tmp_path)
            except OSError:
                print (f"Creation of intermediate {input_file_name} failed")

            sWildcard_file_path = f"{tmp_path}/sWildcard.vpr"
            wildcard_file_path = f"{tmp_path}/wildcard.vpr"

            copyfile(entry.path, sWildcard_file_path)
            copyfile(entry.path, wildcard_file_path)

            with fileinput.FileInput(sWildcard_file_path, inplace=True) as file:
                for line in file:
                    print(line.replace("wildcard", "sWildcard"), end='')

def compile_boogie(conf):
    
    for entry in os.scandir(f"{conf['cwd']}/intermediate"):
        if entry.is_dir():
            print(f"Compiling the program: {os.path.basename(entry.path)}")
            sWildcard_file_path = f"{entry.path}/sWildcard.vpr"
            wildcard_file_path = f"{entry.path}/wildcard.vpr"

            boogie_out_old = f"{entry.path}/old"
            boogie_out_new = f"{entry.path}/new"
            boogie_out_sWildcard = f"{entry.path}/sWildcard"

            sbt_run_command = f"run --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie"
            print_command_old = f"--print {boogie_out_old}.bpl {wildcard_file_path}"
            print_command_new = f"--print {boogie_out_new}.bpl {wildcard_file_path}"
            print_command_sWildcard = f"--print {boogie_out_sWildcard}.bpl {sWildcard_file_path}"

            compile_old = f"cd {conf['carbon_home_old']} && sbt --java-home /usr/lib/jvm/java-11-adoptopenjdk/ '{sbt_run_command} {print_command_old}'"
            compile_new = f"cd {conf['carbon_home_new']} && sbt --java-home /usr/lib/jvm/java-11-adoptopenjdk/ '{sbt_run_command} {print_command_new}'"
            compile_sWildcard = f"cd {conf['carbon_home_new']} && sbt --java-home /usr/lib/jvm/java-11-adoptopenjdk/ '{sbt_run_command} {print_command_sWildcard}'"
            os.system(compile_old)
            os.system(compile_new)
            os.system(compile_sWildcard)

def benchmark(conf):
    
    for entry in os.scandir(f"{conf['cwd']}/intermediate"):
        if entry.is_dir():
            print(f"Benchmarking the program: {os.path.basename(entry.path)}")
            verify_old = "boogie old.bpl"
            verify_new = "boogie new.bpl"
            verify_sWildcard = "boogie sWildcard.bpl"
            benchmarkCommand = f'cd {entry.path} && hyperfine --warmup 3 -M 5 --export-csv measurements.csv "{verify_sWildcard}" "{verify_new}" "{verify_old}"'
            os.system(benchmarkCommand)
            

def get_figures(conf): 
    
    for entry in os.scandir(f"{conf['cwd']}/intermediate"):
        if entry.is_dir():
            program_name = os.path.basename(entry.path)
            print(f"Plotting Performace for the program: {program_name}")

            df = pd.read_csv(f'{entry.path}/measurements.csv')

            # construct some data like what you have:
            mins = df["min"] #np.array([1.19105995984, 1.4093896482100001, 1.0423447737])
            maxes = df["max"] #np.array([1.2903984678399998, 2.49539591321, 1.2176201166999998])
            means = df["mean"] #np.array([1.23751410299, 1.73401861861, 1.0936375535499998])
            std = df["stddev"] #np.array([0.028983541676817333, 0.3306349830887703, 0.04590658218343287])
            labels = np.array(["Symbolic Wildcards", "wildcards (new)", "wildcards (old)"])
            # create stacked errorbars:
            plt.errorbar(labels, means, std, fmt='ok', lw=5)
            plt.errorbar(labels, means, [means - mins, maxes - means],
                        fmt='.k', ecolor='gray', lw=1)
            #plt.xlim(1, 2)
            plt.margins(x=0.3, y=0.1) 
            plt.ylabel("seconds")
            plt.title(f"{program_name} performance")

            #plt.show()
            plt.savefig(f"{conf['output_dir']}/{program_name}.png")
    

if __name__ == '__main__':
    conf = get_config()
    
    setup(conf)

    if conf["compile"]:
        compile_boogie(conf)

    if conf["benchmark"]:
        benchmark(conf)
        get_figures(conf)