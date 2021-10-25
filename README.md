# rep2rep

A framework for encoding the structure of representations and their transformations.

## Getting started

The project is written in Standard ML. You need to have Poly/ML installed: https://polyml.org/.

Build rep2rep by running `make` in the rep2rep directory. Then you can type
```
dist/rep2rep arithDotsDoc
```
to test the one example included in the repo. Doing this should generate a file in the rep2rep/output/latex/ directory called test.tex, from which you can compile a pdf. If you can get this done it means things are working well and you're ready to do something more sophisticated.

## The oruga language
**oruga** is input language for rep2rep. You can find examples of its use in the folder rep2rep/descriptions.

## For developers
If you run `make repl` in the rep2rep directory this will load the basis for rep2rep. Once you are in you can type Standard ML commands. For example run `import "oruga/document"` to load the whole implementation (this particular file import everything).
