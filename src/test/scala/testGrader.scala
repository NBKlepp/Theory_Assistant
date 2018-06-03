import theory._

object testGrader extends App{
  val p = new Parser()
  val m = p.parseFile("Data/M1",_DFA)
}
