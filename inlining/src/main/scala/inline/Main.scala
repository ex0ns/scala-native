package inline

object Main {
  def main(args: Array[String]) : Unit = {
    val c = new C()
    c.x = 10
    println(c.x)
  }

}

class C {
  var x = 5
}
