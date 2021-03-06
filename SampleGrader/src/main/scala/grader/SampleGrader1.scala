/*
  It would probably be best to write a suite of tests that you import
  into the grader so that you don't have to do the same thing over
  and over again. Just an idea.

  Note that we also need to provide the file to find the assignments we want
  to grade with this autograder. That's not the case with the other autograder.

  We coul have hard coded the above information if we wanted to. I didn't.
*/
import TheoryAssistant._

import scala.io.Source
import scala.collection.mutable.Map

object SampleGrader1 extends App{

  //we could just use scores if we didn't want to use the autolab convention
  val scores = Map[String,Int]()

  //the parser we'll use to parse our machines with
  val p = new Parser()
  val exercises = args(0)
  val solDir = "data/solutions1"
  /*
    Just loop through the assignment file parsing each submission machine
    and solution machine in turn and comparing them. If they're the same,
    good. If not, tell the student why not.
  */
  for (line <- Source.fromFile(exercises).getLines){
    print(s"\n\nGrading exercise ${line}...\n")
    var points = 10
    try{

      val sub = p.parseDFA(s"data/submission/${line}")
      val sol = p.parseDFA(s"${solDir}/${line}")

      if ( sub.equals(sol) ) {
         println( s"${line} passed evaluation" )
         scores += line -> points
      } // if

      else {

        println(s"Your submission: \n${sub}")
        val excess_machine = sub.intersect(sol.complement()).minimize()
        val missed_machine = sol.intersect(sub.complement()).minimize()
        if ( !( excess_machine.recognizesEmptyLanguage() )) {
          println(s"-5 points.\n"                                    +
                  s"Your submission accepted some strings that it "  +
                  s"shouldn't have accepted.\n"                      +
                  s"This machine accepts those excessive strings.\n" +
                  s"${excess_machine}")
          points -= 5
        } // if
        if ( !( missed_machine.recognizesEmptyLanguage() )) {
          println(s"-5 points\n"                                           +
                  s"Your submission did not accept all the strings that" +
                  s"it should have.\n "                                  +
                  s"The following machine recognizes those strings: \n"  +
                  s"${missed_machine}")
          points -= 5
        } // if
        scores += line -> points
      } // else
    }catch{
      case pe : ParserException => {println(s"\n${pe}\n");
                                    scores += line -> 0;}
      case nse : NoSubmissionException => {println(s"\n${nse}\n");
                                           scores += line -> 0;}
      case me : MachineException => {println(s"\n${me}\n"); scores += line -> 0}
    } // catch
  } // for
} // SampleGrader
