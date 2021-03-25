import sys, os
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.ticker import LinearLocator
import numpy as np
import pandas as pd





def generate_slow(n_blocks, n_refs):
    
    ref_def = ", ".join(map(lambda i: f"ref{i}: Ref", range(n_refs)))
    begin = "field f: Int \n\n" + f"method main({ref_def})\n" + "{\n"
    end = "\n}"

    inhale_block = "\n".join(map(lambda i: f"   inhale acc(ref{i}.f, wildcard)", range(n_refs)))
    exhale_block = "\n".join(map(lambda i: f"   exhale acc(ref{i}.f, wildcard)", range(n_refs)))

    blocks = "\n".join(map(lambda i: f"{inhale_block}\n{exhale_block}\n", range(n_blocks)))
    code = f"{begin}{blocks}{end}"
    return code

def output(code, tup):

    nb, nr = tup
    with open(f'slow_wildcards/slow_{nb}_{nr}.vpr', 'w') as f:
        sys.stdout = f 
        print(code)

def grid_test():
    grid = [(n_blocks, n_refs) for n_blocks in range(1, 100, 20) for n_refs in range(1, 10, 2)]
    gen_code = map(lambda tup: output(generate_slow(tup[0], tup[1]), tup), grid)
    list(gen_code)

def get_data():
    dfs = []
    for entry in os.scandir("intermediate"):
        if entry.is_dir():
            program_name = os.path.basename(entry.path)
            print(f"Getting data for the program: {program_name}")

            if os.path.exists(f'{entry.path}/measurements.csv'):
                
                _, n_blocks, n_refs = program_name.split("_")
                df = pd.read_csv(f'{entry.path}/measurements.csv')
                df["n_blocks"] = n_blocks
                df["n_refs"] = n_refs

                dfs.append(df)
    df = pd.concat(dfs).groupby("command")
    return df

def plot():    
    

    df = get_data()
    for name, group in df:
        group = group.sort_values(by=["n_blocks", "n_refs"])
        Y = group["n_blocks"]
        X = group["n_refs"]
        Z = group["median"]

        fig, ax = plt.subplots(subplot_kw={"projection": "3d"})
        # Plot the surface.
        surf = ax.plot_trisurf(X, Y, Z, cmap=cm.coolwarm,
                            linewidth=0, antialiased=True)

        # Customize the z axis.
        # ax.set_zlim(-1.01, 1.01)
        ax.zaxis.set_major_locator(LinearLocator(10))
        # A StrMethodFormatter is used automatically
        ax.zaxis.set_major_formatter('{x:.0f}')

        # Add a color bar which maps values to colors.
        fig.colorbar(surf, shrink=0.5, aspect=5)
        plt.title(name)

        ax.view_init(30, -150)
        #plt.savefig(f"figures/3dplot{name}.png")
        plt.show()
        plt.close()

if __name__ == '__main__':
    plot()