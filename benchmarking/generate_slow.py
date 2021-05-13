import sys, os
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.ticker import LinearLocator
import numpy as np
import pandas as pd




def generate_slow_predicate(n_blocks, n_refs):
    
    ref_def = ", ".join(map(lambda i: f"ref{i}: Ref", range(n_refs)))
    begin = "field f: Int \n\n" + "predicate foo(xs:Ref) \n{\n    acc(xs.f)\n}\n\n" + f"method main({ref_def})\n" 
    requires = "\n".join(map(lambda i: f"requires acc(foo(ref{i}), wildcard)", range(n_refs))) + "{\n"
    end = "\n}"
    
    unfold_block = "\n".join(map(lambda i: f"   unfold acc(foo(ref{i}), wildcard)", range(n_refs)))
    fold_block = "\n".join(map(lambda i: f"   fold acc(foo(ref{i}), wildcard)", range(n_refs)))

    blocks = "\n".join(map(lambda i: f"{unfold_block}\n{fold_block}\n", range(n_blocks)))
    code = f"{begin}{requires}{blocks}{end}"

    return code

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
    grid = [(n_blocks, n_refs) for n_blocks in range(1, 20, 10) for n_refs in range(1, 20, 1)]
    gen_code = map(lambda tup: output(generate_slow(tup[0], tup[1]), tup), grid)
    list(gen_code)

def grid_test_predicate():
    grid = [(n_blocks, n_refs) for n_blocks in range(1, 100, 20) for n_refs in range(1, 10, 2)]
    gen_code = map(lambda tup: output(generate_slow_predicate(tup[0], tup[1]), tup), grid)
    list(gen_code)

def get_data(slow_data=False):
    dfs = []
    for entry in os.scandir("intermediate"):
        if entry.is_dir():
            program_name = os.path.basename(entry.path)
            print(f"Getting data for the program: {program_name}")

            if os.path.exists(f'{entry.path}/measurements.csv'):
                df = pd.read_csv(f'{entry.path}/measurements.csv')
                if slow_data:
                    _, n_blocks, n_refs = program_name.split("_")
                    df["n_blocks"] = n_blocks
                    df["n_refs"] = n_refs
                df["program_name"] = program_name
                dfs.append(df)

    df = pd.concat(dfs).groupby("command")
    
    for name, group in df:
        if name == "boogie old_wildcard.bpl":
            old_wildcard = group
        elif name == "boogie map_sWildcard.bpl":
            map_sWildcard = group
        elif name == "boogie map_wildcard.bpl":
            map_wildcard = group
    
    #print(old_wildcard["mean"] / float(map_sWildcard["mean"].sum()))
    #print(old_wildcard, map_sWildcard)
    if slow_data:
        old_wildcard.sort_values(["n_blocks", "n_refs"])
        #print(old_wildcard, map_sWildcard)
        compare_oldW_vs_mapSW = pd.merge(old_wildcard, map_sWildcard, on=["n_blocks", "n_refs"], suffixes=("_old_wildcard", "_map_sWildcard"))
        compare_oldW_vs_mapSW["mean_ratio"] = compare_oldW_vs_mapSW["mean_old_wildcard"] / compare_oldW_vs_mapSW["mean_map_sWildcard"]

        compare_mapW_vs_oldW = pd.merge(map_wildcard, old_wildcard, on=["n_blocks", "n_refs"], suffixes=("_map_wildcard", "_old_wildcard"))
        compare_mapW_vs_oldW["mean_ratio"] = compare_mapW_vs_oldW["mean_map_wildcard"] / compare_mapW_vs_oldW["mean_old_wildcard"]

        compare_mapW_vs_mapSW = pd.merge(map_wildcard, map_sWildcard, on=["n_blocks", "n_refs"], suffixes=("_map_wildcard", "_map_sWildcard"))
        compare_mapW_vs_mapSW["mean_ratio"] = compare_mapW_vs_mapSW["mean_map_wildcard"] / compare_mapW_vs_mapSW["mean_map_sWildcard"]
    else:
        compare_oldW_vs_mapSW = pd.merge(old_wildcard, map_sWildcard, on=["program_name"], suffixes=("_old_wildcard", "_map_sWildcard"))
        compare_oldW_vs_mapSW["mean_ratio"] = compare_oldW_vs_mapSW["mean_old_wildcard"] / compare_oldW_vs_mapSW["mean_map_sWildcard"]

        compare_mapW_vs_oldW = pd.merge(map_wildcard, old_wildcard, on=["program_name"], suffixes=("_map_wildcard", "_old_wildcard"))
        compare_mapW_vs_oldW["mean_ratio"] = compare_mapW_vs_oldW["mean_map_wildcard"] / compare_mapW_vs_oldW["mean_old_wildcard"]

        compare_mapW_vs_mapSW = pd.merge(map_wildcard, map_sWildcard, on=["program_name"], suffixes=("_map_wildcard", "_map_sWildcard"))
        compare_mapW_vs_mapSW["mean_ratio"] = compare_mapW_vs_mapSW["mean_map_wildcard"] / compare_mapW_vs_mapSW["mean_map_sWildcard"]
        #print(compare_oldW_vs_mapSW)
    
    return df, compare_oldW_vs_mapSW, compare_mapW_vs_oldW, compare_mapW_vs_mapSW

def plot_ratio_scratter(compare, name):
    compare.sort_values(["mean_ratio"])
    df = pd.DataFrame({"program_name": compare["program_name"], "ratio": compare["mean_ratio"], "log_ratio": np.log(compare["mean_ratio"])}).sort_values(["ratio"])
    labels = df["program_name"]
    log_ratio = df["log_ratio"]

    programs_where_sWildcard_slower = df[df.ratio < 1]
    programs_where_sWildcard_faster = df[df.ratio > 1]
    print(programs_where_sWildcard_slower)
    
    with open(f"{name}_ratio.csv", 'w', newline='') as csvfile:
        csvfile.write(df.to_csv(index=False))

    fig, ax = plt.subplots()
    # Plot the surface.
    surf = ax.scatter(labels, log_ratio)

    plt.title(name)

    plt.savefig(f"figures/scatter_{name}.png")
    plt.show()
    plt.close()

def plot_ratio(compare, name): 
    
    Y = compare["n_blocks"]
    X = compare["n_refs"]
    Z = np.log(compare["mean_ratio"])
    #print(pd.DataFrame({"n_blocks": Y, "n_refs": X, "ratio": compare["mean_ratio"], "log_ratio": Z}).sort_values(["n_blocks", "n_refs"]))

    fig, ax = plt.subplots(subplot_kw={"projection": "3d"})
    # Plot the surface.
    surf = ax.plot_trisurf(X, Y, Z, cmap=cm.coolwarm,
                        linewidth=0, antialiased=True)

    # Customize the z axis.
    # ax.set_zlim(-1.01, 1.01)
    ax.zaxis.set_major_locator(LinearLocator(10))
    # A StrMethodFormatter is used automatically
    ax.zaxis.set_major_formatter('{x:.2f}')

    # Add a color bar which maps values to colors.
    fig.colorbar(surf, shrink=0.5, aspect=5)
    plt.title(name)

    ax.view_init(30, -150)
    plt.savefig(f"figures/3dplot{name}.png")
    plt.show()
    plt.close()

def plot():    
    df, compare_oldW_vs_mapSW, compare_mapW_vs_oldW, compare_mapW_vs_mapSW = get_data()
    
    # plot_ratio(compare_oldW_vs_mapSW, "oldWildcard_vs_mapSWildcard")
    # plot_ratio(compare_mapW_vs_oldW, "mapWildcard_vs_oldWildcard")
    # plot_ratio(compare_mapW_vs_mapSW, "mapWildcard_vs_mapSWildcard")
    plot_ratio_scratter(compare_oldW_vs_mapSW, "oldWildcard_vs_mapSWildcard") 
    plot_ratio_scratter(compare_mapW_vs_oldW, "mapWildcard_vs_oldWildcard")
    plot_ratio_scratter(compare_mapW_vs_mapSW, "mapWildcard_vs_mapSWildcard")
    return
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
    #grid_test_predicate()
    #get_data()
    #grid_test()