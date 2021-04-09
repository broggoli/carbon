import matplotlib.pyplot as plt
import pandas as pd
import numpy as np
import os, fileinput
from shutil import copyfile
import json

def get_config():
    # default values
    cwd = os.getcwd()
    benchmark_inputs = ["old_baseline", "old_wildcard", "map_baseline", "map_wildcard", "map_sWildcard", "tuple_baseline", "tuple_wildcard", "tuple_sWildcard"],
    with open(f'./config.json', 'r') as f:
        conf = json.load(f)

    conf["cwd"] = cwd

    # Ask user if tool should compile inputs
    while True:
        cmpl = input(f"[{'y' if conf['compile'] else 'n'}] Compile? (y/n)")
        cmpl_low = cmpl.lower()
        if cmpl_low == "":
            break
        elif cmpl_low == "y":
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
        if cmpl_low == "":
            break
        elif benchmark_low == "y":
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
            baseline_file_path = f"{tmp_path}/baseline.vpr"

            copyfile(entry.path, sWildcard_file_path)
            copyfile(entry.path, wildcard_file_path)
            copyfile(entry.path, baseline_file_path)

            # Replace wildcards with sWildcard
            with fileinput.FileInput(sWildcard_file_path, inplace=True) as file:
                for line in file:
                    print(line.replace("wildcard", "sWildcard"), end='')

            # Replace wildcards with baseline
            with fileinput.FileInput(baseline_file_path, inplace=True) as file:
                for line in file:
                    print(line.replace("wildcard", "dummy()"), end='')
           
            with open(baseline_file_path, 'a') as file:
                file.write("\nfunction dummy(): Perm \nensures result > none")

def gen_non_disjunctive(conf):
   pass 

def compile_boogie(conf):
    
    for entry in os.scandir(f"{conf['cwd']}/intermediate"):
        if entry.is_dir():
            print(f"Compiling the program: {os.path.basename(entry.path)}")
            sWildcard_file_path = f"{entry.path}/sWildcard.vpr"
            wildcard_file_path = f"{entry.path}/wildcard.vpr"
            baseline_file_path = f"{entry.path}/baseline.vpr"
            
            def match_input_output(s):
                if "baseline" in s: 
                    return baseline_file_path
                elif "sWildcard" in s:
                    return sWildcard_file_path
                elif "wildcard" in s:
                    return wildcard_file_path

            # only compile files that are not yet compiled
            to_compile = filter(lambda s: not os.path.exists(f"{entry.path}/{s}.bpl"), conf["benchmark_inputs"])
            # generate print commands for compiler
            print_commands = map(lambda s: f"--print {entry.path}/{s}.bpl {match_input_output(s)}", to_compile)

            sbt_run_command = f"run --z3Exe /usr/bin/z3 --boogieExe /bin/boogie/Binaries/boogie"

            def match_version(s):
                if "old" in s:
                    return conf['carbon_home_old']
                elif "tuple" in s:
                    return conf['carbon_home_tuple']
                elif "map" in s:
                    return conf['carbon_home_map']
            
            commands = map(lambda print_command: f"cd {match_version(print_command)} && sbt --java-home /usr/lib/jvm/java-11-adoptopenjdk/ '{sbt_run_command} {print_command}'", print_commands)
            #print(list(commands))
            list(map(lambda command: os.system(command), commands))            
            
def benchmark(conf):
    
    for entry in os.scandir(f"{conf['cwd']}/intermediate"):
        if entry.is_dir():
            print(f"Benchmarking the program: {os.path.basename(entry.path)}")
            # Don't override benchmark files
            if not os.path.exists(f"{entry.path}/measurements.csv"):
                verify_commands = ' '.join(map(lambda s: f'"boogie {s}.bpl"', conf["benchmark_inputs"]))
                benchmarkCommand = f'cd {entry.path} && hyperfine --warmup 3 -M 10 --export-csv measurements.csv {verify_commands}'
                #print(verify_commands)
                os.system(benchmarkCommand)
            

def get_figures(conf): 
    
    for entry in os.scandir(f"{conf['cwd']}/intermediate"):
        if entry.is_dir():
            program_name = os.path.basename(entry.path)
            print(f"Plotting Performace for the program: {program_name}")

            if os.path.exists(f'{entry.path}/measurements.csv'):

                df = pd.read_csv(f'{entry.path}/measurements.csv')

                mins = df["min"] #np.array([1.19105995984, 1.4093896482100001, 1.0423447737])
                maxes = df["max"] #np.array([1.2903984678399998, 2.49539591321, 1.2176201166999998])
                means = df["mean"] #np.array([1.23751410299, 1.73401861861, 1.0936375535499998])
                std = df["stddev"] #np.array([0.028983541676817333, 0.3306349830887703, 0.04590658218343287])
                # only plot what's there
                labels = np.array(list(map(lambda cmd: cmd.split("boogie ")[1].split(".")[0], df["command"])))
                # create stacked errorbars:
                plt.errorbar(labels, means, std, fmt='ok', lw=5)
                plt.errorbar(labels, means, [means - mins, maxes - means],
                            fmt='.k', ecolor='gray', lw=1)
                #plt.xlim(1, 2)
                plt.margins(x=0.3, y=0.1) 
                plt.ylabel("seconds")
                plt.tick_params(axis='x', which='major', labelsize=6)
                plt.title(f"{program_name} performance")

                #plt.show()
                plt.savefig(f"{conf['output_dir']}/{program_name}.png")
                plt.close()
            
            else:
                print("Nothing to plot")
    

if __name__ == '__main__':
    conf = get_config()
    
    setup(conf)

    if conf["compile"]:
        compile_boogie(conf)

    if conf["benchmark"]:
        benchmark(conf)
    get_figures(conf)