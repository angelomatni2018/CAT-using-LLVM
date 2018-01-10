# CAT-using-LLVM
Compiler analysis and transformations written in LLVM passes

## Build
Copy over the pass version you would like into CAT-c/catpass.
Follow the README instructions in CAT-c/, which are the following:
Invoke the script run_me.sh
Add your compiler, located in bin, to your PATH: for example,
```
export PATH=~/CAT/bin
```

## Run
```
cat-c program.c -o binary_name
```