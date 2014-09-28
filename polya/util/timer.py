import timeit
import polya.main.messages as messages
PMUL, PADD, FMMUL, FMADD, FUN, CCM, EXP = range(7)
mod_names = {0: "Poly mult", 1: "Poly add", 2: "FM mult", 3: "FM add", 4: "Function", 5: "CCM",
             6: 'Exponential'}

runs = {}
time_total = {}
time_cur = {}


def start(module):
    for k in [k for k in time_cur if time_cur[k] != 0]:
        e_stop(k)
    time_cur[module] = timeit.default_timer()


def e_stop(module):
    t = timeit.default_timer() - time_cur[module]
    time_total[module] = time_total.get(module, 0) + t
    time_cur[module] = 0
    runs[module] = runs.get(module, 0) + 1
    return t


def stop(module):
    t = e_stop(module)
    messages.announce("Module run time: " + str(round(t, 3)), messages.DEBUG)


def announce_times():
    for k in [k for k in time_cur if time_cur[k] != 0]:
        e_stop(k)
    messages.announce("Average run times:", messages.DEBUG)
    for i in time_total:
        messages.announce(
            "{0!s} module: {1!s} over {2!s} runs".format(mod_names[i],
                                                         str(round(time_total[i]/runs[i], 3)),
                                                         runs[i]),
            messages.DEBUG)