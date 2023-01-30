import "oruga.document";

signature CPARSERS =
sig
  val parseProbSys : string -> Construction.construction;
end

structure CParsers : CPARSERS =
struct

  fun parseProbSys s =
      let val dContent = Document.read "bTreeBayes"
          val KB = Document.knowledgeOf dContent
          val stringConSpecData = Document.findConSpecWithName dContent "string"
          val btreeConSpecData = Document.findConSpecWithName dContent "btree"
          val bayesConSpecData = Document.findConSpecWithName dContent "bayesPlus"
          val interStringBTreeConSpecData = Document.findConSpecWithName dContent "interStringBTree"
          val interBTreeBTreeConSpecData = Document.findConSpecWithName dContent "interBTreeBTree"
          val interBTreeBayesConSpecData = Document.findConSpecWithName dContent "interBTreeBayes"
          fun getTopConstruction st =
              hd (List.flatmap Composition.resultingConstructions (State.patternCompsOf st));
          val stringConstruction = Lift.string (Document.normaliseString s)

          val goal0 = Document.parseConstruction interStringBTreeConSpecData (":metaTrue <- TREEIFY[t:" ^ (Document.normaliseString s) ^ ":string,t':btree]")
          val state0 = Transfer.initState stringConSpecData btreeConSpecData interStringBTreeConSpecData false KB stringConstruction goal0

          val btree1 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 100) false NONE state0))
          (*val _ = print (Construction.toString btree1 ^ "\n\n") *)
          val construct1 = Construction.constructOf btree1
          val goal1 = Document.parseConstruction interBTreeBTreeConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct1) ^ ",t':btree]")
          val state1 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeConSpecData false KB btree1 goal1

          val btree2 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 100) false NONE state1))
          (*val _ = print (Construction.toString btree2 ^ "\n\n") *)
          val construct2 = Construction.constructOf btree2
          val goal2 = Document.parseConstruction interBTreeBTreeConSpecData (":metaTrue <- SEMICOLON[" ^ (CSpace.stringOfToken construct2) ^ ",t':btree]")
          val state2 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeConSpecData false KB btree2 goal2

          val btree3 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 100) false NONE state2))
          (*val _ = print (Construction.toString btree3 ^ "\n\n") *)
          val construct3 = Construction.constructOf btree3
          val goal3 = Document.parseConstruction interBTreeBTreeConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct3) ^ ",t':btree]")
          val state3 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeConSpecData false KB btree3 goal3

          val btree4 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 50) false NONE state3))
          (*val _ = print (Construction.toString btree4 ^ "\n\n") *)
          val construct4 = Construction.constructOf btree4
          val goal4 = Document.parseConstruction interBTreeBTreeConSpecData (":metaTrue <- SPACE[" ^ (CSpace.stringOfToken construct4) ^ ",t':btree]")
          val state4 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeConSpecData false KB btree4 goal4

          val btree5 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 100) false NONE state4))
          (*val _ = print (Construction.toString btree5 ^ "\n\n") *)
          val construct5 = Construction.constructOf btree5
          val goal5 = Document.parseConstruction interBTreeBTreeConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct5) ^ ",t':btree]")
          val state5 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeConSpecData false KB btree5 goal5

          val btree6 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 50) false NONE state5))
          (*val _ = print (Construction.toString btree6 ^ "\n\n") *)
          val construct6 = Construction.constructOf btree6
          val goal6 = Document.parseConstruction interBTreeBTreeConSpecData (":metaTrue <- MID[" ^ (CSpace.stringOfToken construct6) ^ ",t':btree]")
          val state6 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeConSpecData false KB btree6 goal6

          val btree7 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 100) false NONE state6))
          (*val _ = print (Construction.toString btree7 ^ "\n\n") *)
          val construct7 = Construction.constructOf btree7
          val goal7 = Document.parseConstruction interBTreeBTreeConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct7) ^ ",t':btree]")
          val state7 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeConSpecData false KB btree7 goal7

          val btree8 = getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 3, NONE, SOME 50) false NONE state7))
          (*val _ = print (Construction.toString btree8 ^ "\n\n") *)
          val construct8 = Construction.constructOf btree8
          val goal8 = Document.parseConstruction interBTreeBayesConSpecData (":metaTrue <- SYS[" ^ (CSpace.stringOfToken construct8) ^ ",t':probSys]")
          val state8 = Transfer.initState btreeConSpecData bayesConSpecData interBTreeBayesConSpecData false KB btree8 goal8
      in getTopConstruction (Seq.hd (Transfer.structureTransfer (SOME 4, NONE, SOME 200) false NONE state8))
      end
end
