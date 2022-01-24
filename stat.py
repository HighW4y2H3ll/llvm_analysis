

'''
Stats on the minimizer for the number of functions && bc file size.
Evaluate the original bc file, the old minizier output, the new minizier output, and the new minizier output with cutoff function list

Get function # stat in log files; bc file size from output bc.
'''

X86_BC_PATH="/opt/zhenghao/llvm6bcfiles"
SPARC_BC_PATH="/opt/sparc_bc_files/svc_bc_new"

OLD_OUTPUT_PATH="/opt/zhenghao/llvm-mirror/build/output"
OLD_LOG_PATH="/opt/zhenghao/llvm-mirror/build/log"

NEW_OUTPUT_PATH="/opt/zhenghao/output"
NEW_LOG_PATH="/opt/zhenghao/log"


import os


def parseLogFile(filedir):
    with open(filedir, 'r') as fd:
        for line in fd.read().split('\n'):
            if line.startswith("REDUCED LLVM FILE BY") and "(union set)" in line:
                return float(line.split()[4].strip('%'))/100

def statFuncNum(filename, PREFIX):
    stat = []
    stat.append(parseLogFile(os.path.join(OLD_LOG_PATH, PREFIX, "log_" + filename)))
    stat.append(parseLogFile(os.path.join(NEW_LOG_PATH, PREFIX, "log_" + filename)))
    stat.append(parseLogFile(os.path.join(NEW_LOG_PATH, PREFIX, "cutlog_" + filename)))
    return stat

def sysFileSz(filedir):
    si = os.stat(filedir)
    return si.st_size

def statFileSz(filename, PREFIX):
    stat = []
    if PREFIX == "x86":
        orig = float(sysFileSz(os.path.join(X86_BC_PATH, filename)))
    elif PREFIX == "sparc":
        orig = float(sysFileSz(os.path.join(SPARC_BC_PATH, filename)))
    stat.append(sysFileSz(os.path.join(OLD_OUTPUT_PATH, PREFIX, "new_" + filename)) / orig)
    stat.append(sysFileSz(os.path.join(NEW_OUTPUT_PATH, PREFIX, "new_" + filename)) / orig)
    stat.append(sysFileSz(os.path.join(NEW_OUTPUT_PATH, PREFIX, "cutoff_" + filename)) / orig)
    return stat

def parseLogTime(filedir):
    with open(filedir, 'r') as fd:
        for line in fd.read().split('\n'):
            if line.startswith("real"):
                return float(line.split()[1].split('m')[0])

def statTime(filename, PREFIX):
    stat = []
    stat.append(parseLogTime(os.path.join(NEW_LOG_PATH, PREFIX, filename + ".time")))
    stat.append(parseLogTime(os.path.join(NEW_LOG_PATH, PREFIX, "cutoff_" + filename + ".time")))
    return stat

def statByArch(ROOT_DIR, PREFIX):
    bcFuncNum = {}  # % of functions after minimize: { bcfilename : [ old minizier, new minizier, new minizier with cutoff ] }
    bcFileSz = {}   # % of file size after minimize: { bcfilename : [ old minizier, new minizier, new minizier with cutoff ] }
    execTime = {}
    if PREFIX == "x86":
        bcdir = X86_BC_PATH
    elif PREFIX == "sparc":
        bcdir = SPARC_BC_PATH
    for root, dirs, files in os.walk(bcdir):
        for f in files:
            if not f.endswith(".bc"):
                continue
            if PREFIX == "x86" and f == "delivergie.bc":
                continue
            bcFuncNum[f] = statFuncNum(f, PREFIX)
            bcFileSz[f] = statFileSz(f, PREFIX)
            execTime[f] = statTime(f, PREFIX)
    return bcFuncNum, bcFileSz, execTime




x86_fn, x86_fsz, x86_et = statByArch(X86_BC_PATH, "x86")
sparc_fn, sparc_fsz, sparc_et = statByArch(SPARC_BC_PATH, "sparc")


# Plot
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

def doPlot(data, msg, out):
    barwidth = 0.35
    fig, ax = plt.subplots()
    xtic_label = list(data.keys())
    xtic = range(len(xtic_label))
    old_mini = [100*data[k][0] for k in xtic_label]
    new_mini = [100*data[k][1] for k in xtic_label]
    new_cutoff = [100*data[k][2] for k in xtic_label]
    plot_old = ax.bar([i-barwidth for i in xtic], old_mini, label="old minizier", width=barwidth)
    plot_new = ax.bar(xtic, new_mini, label="new minizier", width=barwidth)
    plot_cutoff = ax.bar([i+barwidth for i in xtic], new_cutoff, label="new minizier with cutoff", width=barwidth)
    ax.set_xlabel("bc files")
    ax.set_ylabel("percentage to the original")
    ax.legend()
    ax.set_xticks(xtic)
    ax.set_xticklabels(xtic_label, rotation=90)
    #ax.set_yticks(range(100))
    ax.set_title(msg)
    #fig.set_size_inches(100, 100)   # BOOOM!
    plt.subplots_adjust(right=200)
    fig.set_size_inches(70, 10)
    fig.tight_layout()
    fig.savefig(out)
    plt.clf()

def doHistPlot(data, msg, out):
    fig, ax = plt.subplots()
    xtic_label = list(data.keys())
    old_mini = [100*data[k][0] for k in xtic_label]
    new_mini = [100*data[k][1] for k in xtic_label]
    new_cutoff = [100*data[k][2] for k in xtic_label]
    #ax.hist([old_mini, new_mini, new_cutoff], histtype='step', cumulative=True, bins=20, label=["old minimizer", "new minimizer", "new minizier with cutoff"])
    ax.hist([old_mini, new_mini, new_cutoff], histtype='step', cumulative=False, bins=20, label=["old minimizer", "new minimizer", "new minizier with cutoff"])
    ax.set_xlabel("output file size to the original size(%)")
    ax.set_ylabel("# of bc files")
    ax.set_title(msg)
    ax.legend(loc="upper left")
    fig.savefig(out)
    plt.clf()

def doTimeHistPlot(data, msg, out):
    fig, ax = plt.subplots()
    xtic_label = list(data.keys())
    new_mini = [data[k][0] for k in xtic_label]
    new_cutoff = [data[k][1] for k in xtic_label]
    #ax.hist([old_mini, new_mini, new_cutoff], histtype='step', cumulative=True, bins=20, label=["old minimizer", "new minimizer", "new minizier with cutoff"])
    ax.hist([new_mini, new_cutoff], histtype='step', cumulative=False, bins=20, label=["new minimizer", "new minizier with cutoff"])
    ax.set_xlabel("exec time in minutes")
    ax.set_ylabel("# of bc files")
    ax.set_title(msg)
    ax.legend(loc="upper left")
    fig.savefig(out)
    plt.clf()


doPlot(x86_fn, "x86 function number reduced", "x86_func_num.png")
doPlot(x86_fsz, "x86 output file size", "x86_file_size.png")
doPlot(sparc_fn, "sparc function number reduced", "sparc_func_num.png")
doPlot(sparc_fsz, "sparc output file size", "sparc_file_size.png")

doHistPlot(x86_fsz, "x86 output file size histogram", "x86_file_size_hist.png")
doHistPlot(sparc_fsz, "sparc output file size histogram", "sparc_file_size_hist.png")

doTimeHistPlot(x86_et, "x86 minimizier execution time histogram", "x86_exec_time_hist.png")
doTimeHistPlot(sparc_et, "sparc minimizier execution time histogram", "sparc_exec_time_hist.png")
