Installation instructions
=========================

Setting your Python path
------------------------

To run Polya, the Polya module needs to be in your Python path. For example, in a Unix bash shell, use

    export PYTHONPATH=PYTHONPATH:path/to/directory

where "directory" contains the contents of the distribution, including the folder named "polya". If you will be using Polya regularly, it is convenient to add this line to your .bashrc.

In Windows, open a command prompt window and type

    set PYTHONPATH=%PYTHONPATH%;C:\Path\to\directory

Or select My Computer > Properties > Advanced System Settings > Environment Variables and create (or modify) the PYTHONPATH variable to include C:\Path\to\directory


Installing the geometry packages
--------------------------------

Polya can make use of more efficient geometric methods to handle additive and multiplicative information. To to take advantage of these capabilities, you need to have the following software installed:

1. The Gnu Multiple Precision library, [GMP](https://gmplib.org/). Typically you can install this using a package manager on Unix systems, and it will usually provided in the binary for Windows systems.

2. Komei Fukuda's [cddlib](https://pypi.python.org/pypi/pycddlib/#downloads), with Python bindings. Use [EasyInstall](http://peak.telecommunity.com/DevCenter/EasyInstall) on Unix platforms, and get the binaries (.exe) for Windows.

3. David Avis' [lrs and redund](http://cgm.cs.mcgill.ca/~avis/C/lrs.html). 

   a. Linux or Windows: download the appropriate binary file ([Linux](http://cgm.cs.mcgill.ca/~avis/C/lrslib/binaries/linux/), [Windows](http://cgm.cs.mcgill.ca/~avis/C/lrslib/binaries/windows/)) and put the binary file in 
   
       /Path/to/Polya/polya/polyhedron

   b. Other systems: follow the instructions [here](http://cgm.cs.mcgill.ca/~avis/C/lrslib/USERGUIDE.html#Installation%20Section).

