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
          val stringConSpecData = Document.getConSpecWithName dContent "stringRich"
          val btreeConSpecData = Document.getConSpecWithName dContent "btree"
          val bayesConSpecData = Document.getConSpecWithName dContent "bayesG"
          val interStringBTreeConSpecData = Document.getConSpecWithName dContent "interStringBTree"
          val interBTreeBTreeSPACEConSpecData = Document.getConSpecWithName dContent "interBTreeBTreeSPACE"
          val interBTreeBTreeSIMPLIFYConSpecData = Document.getConSpecWithName dContent "interBTreeBTreeSIMPLIFY"
          val interBTreeBTreeSEMICOLONConSpecData = Document.getConSpecWithName dContent "interBTreeBTreeSEMICOLON"
          val interBTreeBTreeMIDConSpecData = Document.getConSpecWithName dContent "interBTreeBTreeMID"
          val interBTreeBayesConSpecData = Document.getConSpecWithName dContent "interBTreeBayes"
          fun getTopConstruction st =
              hd (List.flatmap Composition.resultingConstructions (State.patternCompsOf st));
          val normalisedString = Document.normaliseString s
          val stringConstruction = Lift.string normalisedString

          val goal0 = Document.parseConstruction interStringBTreeConSpecData (":metaTrue <- TREEIFY[t:" ^ normalisedString ^ ":string,t':btree]")
          val state0 = Transfer.initState stringConSpecData btreeConSpecData interStringBTreeConSpecData false KB stringConstruction goal0

          val result0 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state0))
          val _ = if length (State.goalsOf result0) > 0 then print "WARNING: step 0 of parsing was incomplete \n" else ()

          val btree1 = getTopConstruction result0
          (*val _ = print (Construction.toString btree1 ^ "\n\n") *)
          val construct1 = Construction.constructOf btree1
          val goal1 = Document.parseConstruction interBTreeBTreeSIMPLIFYConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct1) ^ ",t':btree]")
          val state1 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeSIMPLIFYConSpecData false KB btree1 goal1

          val result1 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state1))
          val _ = if length (State.goalsOf result1) > 0 then print "WARNING: step 1 of parsing was incomplete \n" else ()

          val btree2 = getTopConstruction result1
          (*val _ = print (Construction.toString btree2 ^ "\n\n") *)
          val construct2 = Construction.constructOf btree2
          val goal2 = Document.parseConstruction interBTreeBTreeSEMICOLONConSpecData (":metaTrue <- SEMICOLON[" ^ (CSpace.stringOfToken construct2) ^ ",t':btree]")
          val state2 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeSEMICOLONConSpecData false KB btree2 goal2

          val result2 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state2))
          val _ = if length (State.goalsOf result2) > 0 then print "WARNING: step 2 of parsing was incomplete \n" else ()

          val btree3 = getTopConstruction result2
          (*val _ = print (Construction.toString btree3 ^ "\n\n") *)
          val construct3 = Construction.constructOf btree3
          val goal3 = Document.parseConstruction interBTreeBTreeSIMPLIFYConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct3) ^ ",t':btree]")
          val state3 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeSIMPLIFYConSpecData false KB btree3 goal3

          val result3 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state3))
          val _ = if length (State.goalsOf result3) > 0 then print "WARNING: step 3 of parsing was incomplete \n" else ()

          val btree4 = getTopConstruction result3
          (*val _ = print (Construction.toString btree4 ^ "\n\n") *)
          val construct4 = Construction.constructOf btree4
          val goal4 = Document.parseConstruction interBTreeBTreeSPACEConSpecData (":metaTrue <- SPACE[" ^ (CSpace.stringOfToken construct4) ^ ",t':btree]")
          val state4 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeSPACEConSpecData false KB btree4 goal4

          val result4 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state4))
          val _ = if length (State.goalsOf result4) > 0 then print "WARNING: step 4 of parsing was incomplete \n" else ()

          val btree5 = getTopConstruction result4
          (*val _ = print (Construction.toString btree5 ^ "\n\n") *)
          val construct5 = Construction.constructOf btree5
          val goal5 = Document.parseConstruction interBTreeBTreeSIMPLIFYConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct5) ^ ",t':btree]")
          val state5 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeSIMPLIFYConSpecData false KB btree5 goal5

          val result5 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state5))
          val _ = if length (State.goalsOf result5) > 0 then print "WARNING: step 5 of parsing was incomplete \n" else ()

          val btree6 = getTopConstruction result5
          (*val _ = print (Construction.toString btree6 ^ "\n\n") *)
          val construct6 = Construction.constructOf btree6
          val goal6 = Document.parseConstruction interBTreeBTreeMIDConSpecData (":metaTrue <- MID[" ^ (CSpace.stringOfToken construct6) ^ ",t':btree]")
          val state6 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeMIDConSpecData false KB btree6 goal6

          val result6 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state6))
          val _ = if length (State.goalsOf result6) > 0 then print "WARNING: step 6 of parsing was incomplete \n" else ()

          val btree7 = getTopConstruction result6
          (*val _ = print (Construction.toString btree7 ^ "\n\n") *)
          val construct7 = Construction.constructOf btree7
          val goal7 = Document.parseConstruction interBTreeBTreeSIMPLIFYConSpecData (":metaTrue <- SIMPLIFY[" ^ (CSpace.stringOfToken construct7) ^ ",t':btree]")
          val state7 = Transfer.initState btreeConSpecData btreeConSpecData interBTreeBTreeSIMPLIFYConSpecData false KB btree7 goal7

          val result7 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state7))
          val _ = if length (State.goalsOf result7) > 0 then print "WARNING: step 7 of parsing was incomplete \n" else ()

          val btree8 = getTopConstruction result7
          (*val _ = print (Construction.toString btree8 ^ "\n\n") *)
          val construct8 = Construction.constructOf btree8
          val goal8 = Document.parseConstruction interBTreeBayesConSpecData (":metaTrue <- SYS[" ^ (CSpace.stringOfToken construct8) ^ ",t':probSys]")
          val state8 = Transfer.initState btreeConSpecData bayesConSpecData interBTreeBayesConSpecData false KB btree8 goal8

          val result8 = (Seq.hd (Transfer.structureTransfer (SOME 6, NONE, NONE) true false NONE state8))
          val _ = if length (State.goalsOf result8) > 0 then print "WARNING: step 8 of parsing was incomplete \n" else ()

      in getTopConstruction result8
      end
end
