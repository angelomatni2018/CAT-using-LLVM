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

## How It Works
### Task at hand
This compiler handles the CAT api, a wrapper around a struct containing an integer. This abstraction is in place so that normal compiler optimizations don't completely replace the api. The api provides ways to create this CAT struct, add two structs together, subtract them, and get the integer value of one. The compiler's job is to use constant propogation and constant folding to optimize the CAT api as a normal compiler would optimize basic integer operations.

### Approach
Full Description to come soon.

For now, I first created a reaching definition DFA, and then employed constant propogation on each CAT_get api call to see if it could be replaced with a constant integer.
