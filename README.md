# Oruga

A framework for encoding the structure of representations and their transformations.

## Getting started

The project is written in Standard ML. You need to have Poly/ML installed: https://polyml.org/.

Build rep2rep by running `make` in the rep2rep directory. Then you can type
```
dist/rep2rep test
```
to test a batch of examples included in our library. If you have created your own oruga input file you can replace `test` with your file. Doing this should generate latex files in the rep2rep/output/latex/ directory, which you can compile into pdf. If you can get this done it means things are working well and you're ready to do something more sophisticated.

## The input language
We have an input language for specifying type systems, constructor specifications, graphs, and schemas. You can find examples of its use in the folder rep2rep/input.

## For developers
If you run `make repl` in the rep2rep directory this will load the basis for rep2rep. Once you are in you can type Standard ML commands. For example run `import "oruga/document"` to load the whole implementation (this particular file import everything).
