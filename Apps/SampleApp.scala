package TheoryAssistant
import TypeDefs._

object SampleApp extends App{
  val p = new Parser()
    val submission_machine = args(1)
    val solution_machine = args(2)

    val sub = p.parseDFA(submission_machine)
    val sol = p.parseDFA(solution_machine)

    if ( sub.equals(sol) ) println( s"machine ${sub.getName} passed" )
    else {
      println("Your submission: ${sub}")
      val excess_machine = sub.intersect(sol.complement()).minimize()
      val missed_machine = sol.intersect(sub.complement()).minimize()
      if ( !( excess_machine.recognizesEmptyLanguage() )) {
        println(s"Your submission recognized some strings that it
                 | shouldn't have accepted: \n
                 | ${excess_machine}".stripMargin)
      } // if 
      if ( !( missed_machine.recognizesEmptyLanguage() )) {
        println(s"Your submission did not accept all the strings that
                 | it should have: \n${missed_machine}".stripMargin)
      } // if
    } // else
}
