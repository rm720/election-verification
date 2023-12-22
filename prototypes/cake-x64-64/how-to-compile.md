How to compile caleML executable on Mac M1
date: 02-07-2023

1. 
Get latest versions

For both repos HOL and CakeML:
pull from upstream, use the commits from regression tests:
https://cakeml.org/regression.cgi
HOL: 
git checkout develop  
git fetch    
git pull upstream develop  
git reset --hard 3ce4e26  
CakeML: Similar to above

Update stuff (or install follow this https://github.com/HOL-Theorem-Prover/HOL/blob/develop/INSTALL)
upgrade polyml:
in terminal run
brew update
brew upgrade poly_ml

update HOL
cd YOUR_HOL_DIR
git clean -xdf
bin/build cleanAll     
bin/build  
wait 3 hours approx.

Hol building will have error in zc2hs. 
It does not hurt somehow, ignore it.


2. 
Go to cakeML/examples/solutions
For every executable program you need 3 files in one directory:
NameProgPcropt.sml
NameProofScript.sml
NameCompileScript.sml
and Holmake file with all the pathes of the libraries used
Run Holmake in the directory
This will create 3 .sig files 
and Name.S file

4.
Copy Name.S to the directory with cake makefile (cake-x64-64).

run:
make clean
cc  cake.S basis_ffi.c   -D__EVAL__ -o cake
cc  crypto.S basis_ffi.c   -o crypto
./crypto

git checkout ff6e145   

git checkout v2117    # cakeML
