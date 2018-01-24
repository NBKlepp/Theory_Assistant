package theory

import scala.collection.mutable.{Set,Map}
import TypeDefs._
import scala.io.Source
import java.io.{PrintWriter,FileWriter}

object SubmissionGrader extends App{


       val DEBUG = false
       print(s"args: ${args.deep}")
       val name = args(0)
       val solution = args(1)
       val HW = args(2)
    
       val j = name.indexOf(".txt")
       

       val nname = name.substring(0,j)
       val inFiles  = Array(s"data/${HW}/${name}",s"data/${solution}")

       val outFile = s"data/OutFiles/${HW}/${nname}Out"
       val fw = new FileWriter(outFile)
       val pw = new PrintWriter(fw)

       val submissionMachines = Map[String,NFA]()
       val answerMachines     = Map[String,NFA]()

       var machines = Array(submissionMachines,answerMachines)

       var workingOn      = ""
       val machineStates  = Array(Map[String,Set[State]](),Map[String,Set[State]]())
       val machineSigmas  = Array(Map[String,Set[Symbl]](),Map[String,Set[Symbl]]())
       val machineDeltas  = Array(Map[String,Set[((State,Symbl),Set[State])]](),Map[String,Set[((State,Symbl),Set[State])]]())
       val machineStarts  = Array(Map[String,State](),Map[String,State]())
       val machineAccepts = Array(Map[String, Set[State]](),Map[String, Set[State]]())
       //val machineTypes	  = Array(Map[String,Int](),Map[String,Int]())
       val machineNames   = Array(Set[String](),Set[String]())

try{
       for ( i <- 0 to 1 ) {
       	   val str = if (i==0) "submissions" else "answers"
	   println(s"************************making ${str} machines**********************************")
       	   val machineMap = machines(i)

	   for ( lline <- Source.fromFile(inFiles(i)).getLines ){
       	       val line = lline.replace("\\e",epsilon)
	       if (DEBUG) println(s"Current line: |$line|")
	       if (line.length > 0 ){
       	       line.charAt(0) match{
	           case '%' => changeWork(line,i)
	       	   case 'Q' => makeStates(line,i)
	       	   case 'S' => makeSigma(line,i)
	       	   case 'd' => makeDelta(line,i)
	       	   case 'q' => makeStart(line,i)
	       	   case 'F' => makeFinal(line,i)
	       	   case _   => 
	       } // match
	       } // if
           } // for line       
       } // for i

       if(DEBUG){
        println("**************                 CHECK OUT THESE MACHINE NAMES                   ********************")
	for (name <- machineNames) println(s"machineNames: ${name}")
       }
       
       def makeFinal(line : String, i : Int){
       	   if (DEBUG) println("\t\t**************MAKING FINAL**************")
           val tokens = line.replace("F={"," ").replace("};"," ").replace(","," ").split(" ").map( x => x.trim() ).filter( (x : String) => x.length > 0 )
	   if (DEBUG){
	      for (t <- tokens ) println(s"token: |$t|")
	   }// println(s"Tokens for final: ${tokens.deep}")
	   val accept = Set[State]()
	   for ( t <- tokens ) accept += t
	   if (DEBUG) println(s"final is : $accept")
	   machineAccepts(i) += workingOn -> accept
       }

       def makeStart(line : String,i : Int){
       	   val tokens = line.replace("q0="," ").replace(";"," ").split(" ").map( x => x.trim() ).filter( (x : String) => x.length > 0 )
	   val start = if (tokens.size == 1 ) tokens(0) else ""
	   machineStarts(i) += workingOn -> start
       }

       def makeDelta(line : String,i : Int){
       	   //val delta = Map[(State,Symbl),Set[State]]()
	   if (DEBUG) println(s"Making delta from $line")
       	   val tokens = line.split("=")
	   if (DEBUG) println(s"Tokens: ${tokens.deep}")
	   val iinput = if ( tokens.size >0 ) 
	        tokens(0).replace("d("," ").replace(")"," ").replace(","," ").split(" ").map( x => x.trim() ).filter( (x :String) => x.length > 0 )
	    		else Array("","")
	   if (DEBUG) println(s"resulting iinput: ${iinput.deep}, iinput.length: ${iinput.length}")
	   if (DEBUG) println(s"iinput(0) : |${iinput(0)}|, iinput(1): |${iinput(1)}|")
	   val input = (iinput(0),iinput(1))
	   val ooutput = if (tokens.size > 1 )
	       	      	tokens(1).replace("{"," ").replace("};"," ").replace(","," ").replace(";"," ").split(" ").map( x => x.trim() ).filter( (x : String) => x.length > 0 )
			else
			Array("")
	   val output = Set[State]()
	   for ( o <- ooutput ) {
	       if (DEBUG) println(s"adding |$o| to the output for the input.")
	       output += o
	   }
	   //if (output.size > 1) machineTypes(workingOn) = 1
	   if ( machineDeltas(i) contains workingOn) machineDeltas(i)(workingOn) += ((input,output))
	   else{
		machineDeltas(i) += workingOn -> Set[((State,Symbl),Set[State])]()
		machineDeltas(i)(workingOn) += ((input,output))
	   } // else
	   if (DEBUG) println(s"delta after this delta iteration, machinDeltas($i)($workingOn): ${machineDeltas(i)(workingOn)}")
       }

       def makeStates(line : String,i : Int){
       	   if (DEBUG) println(s"Making states.")
       	   var tokens = line.replace("Q={"," ").replace(","," ").replace("};"," ").split(" ").map( x => x.trim() ).filter( (x : String) => x.length > 0 )
	   val states = Set[State]()
	   for ( t <- tokens ) states += t
	   machineStates(i) += workingOn -> states
	   if (DEBUG) println(s"States made: $states")
       }

       def makeSigma(line : String,i : Int){
       	   if (DEBUG) println(s"Making sigma.")
       	   var tokens = line.replace("S={"," ").replace(","," ").replace("};"," ").split(" ").map( x => x.trim() ).filter( (x : String) => x.length > 0 )
	   val sigma = Set[Symbl]()
	   for ( t <- tokens ) sigma += t
	   machineSigmas(i) += workingOn -> sigma
	   if (DEBUG) println(s"Sigma made: $sigma")
	   
       }

       def changeWork(line : String,i : Int){
       	   val str = if (i==0) "submissions" else "answers"
	   println(s"making ${str} machines")
	   val tokens = line.replace("title=\""," ").replace("\";"," ").replace("%"," ").split(" ").map( x => x.trim() ).filter( (x : String) => x.length > 0 )
           workingOn = if (tokens.size > 0 ) tokens(0) else ""
	   machineNames(i) += workingOn
	   if (DEBUG) println(s"made a new name: |$workingOn|")
	   if (DEBUG) println(s"machineNames(${str}): ${machineNames(i)}")
	   //machineTypes += workingOn -> 0
       }


       for ( i <- 0 to 1 ){
       	   if (DEBUG) println(s"\t\t**********Making machines i: $i***************")
	   val str = if (i==0) "submissions" else "answers"
	   println(s"making ${str} machines")
       	   for ( name <- machineNames(i) ) {
	       if (DEBUG) {
	       	  println(s"machineAccepts(i): ${machineAccepts(i)}")
	       }
       	       val states = machineStates(i)(name)
	       val sigma  = machineSigmas(i)(name)
	       val delta  = machineDeltas(i)(name)
	       val start  = machineStarts(i)(name)
	       val accept = machineAccepts(i)(name)
	       val m      = new NFA(states,sigma,delta,start,accept,name)
	       machines(i) += name -> m
	       if (DEBUG) println(s"\t\t******MADE NEW MACHINE********\n ${submissionMachines(name)}\n")
           }
       }
       
       val results = Map[String,String]()
       var points = 0.0
       var avail = 0.0
       for ( machine <- machines(1)  ) {
       	   points += 1.0
	   avail += 10
       	   val name = machine._1
	   val m    = machine._2
	   val mm   = machines(0).getOrElse(name,new NFA())
	   var failVal = 0.0
	   if ( (submissionMachines contains name) && submissionMachines(name).isValid() ){
	      //println(s"Submission machine accepts: ${GNFA.convert(mm)}")
	      //println(s"Answer machine accepts: ${GNFA.convert(m)}")
	      val res = m.equals(mm)
	      val resString = if (res) "pass" else "fail"
	      println(s"Testing equality for $name: $resString")
	      pw.println(s"Testing equality for $name: $resString\n")
	      if (res) {
	      	 results += name -> "pass"
	      }
 	      if (!res){
	      	 println(s"\tOne correct machine was: $m")
		 println(s"\tYour submission machine was: $mm")
		 
		 pw.println(s"\tOne correct machine was: $m")
		 pw.println(s"\tYour submission machine was: $mm")
		 
		 //val rex1 = GNFA.convert(m)
		 //val rex2 = GNFA.convert(mm)
		 val m3 = m.intersect(mm.complement())
		 val m4 = mm.intersect(m.complement())
	      	 //println(s"Strings you didn't get: ${rex1}")
		 //println(s"Strings you shouldn't have gotten: ${rex2}")
		 if ( !(m3.DFAify().recognizesEmptyLanguage()) ) {
		    println(s"\tYou received half off because your machine didn't accept all the strings it should have")
		    pw.println(s"\tYou received half off because your machine didn't accept all the strings it should have")
		    failVal += .5
		 }
		 if ( !(m4.DFAify().recognizesEmptyLanguage()) ){
		    println(s"\tYou received half off because your machine accepted some strings it shouldn't have.")
		    pw.println(s"\tYou received half off because your machine accepted some strings it shouldn't have.")
		    failVal += .5
		 }
		 results += name -> s"fail : $failVal}"
	      }
	      
	   } // if
	   else if ( (submissionMachines contains name) && !(submissionMachines(name).isValid()) ) {
	   	println(s"Machine submission for $name was invalid specifications")
	   	pw.println(s"Machine submission for $name was invalid specifications")		
		failVal = 1
		results += name -> s"fail : $failVal"
	   }
	   else {
	   	failVal = 1
	   	println(s"No valid submission found for $name.")
		pw.println(s"No valid submission found for $name.")
		results += name -> s"fail : $failVal"
	   }
	   points -= failVal
       }

       println(s"Final Results:")
       pw.println(s"Final Results:")
       for( (k,v) <- results ) {
       	    println(s"$k : $v")
	    pw.println(s"$k : $v")
       }
       println(s"Points: ${points*10} out of ${avail}")
       pw.println(s"Points: ${points*10} out of ${avail}")
       
       } catch{
       	 case e => {
	      println(s"Error in running autograder: $e")
	      println(s"${e.getStackTrace.mkString("\n")}")

	      pw.println(s"Error in running autograder: $e")
	      pw.println(s"${e.getStackTrace.mkString("\n")}")

	 }
	 
       }
       pw.close()
}