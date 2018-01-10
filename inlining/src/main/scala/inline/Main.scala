package inline

object Main {
  def main(args: Array[String]) : Unit = {
  }

  def create() : Unit = {
    println("This is create")
    addFive(4) + addSix(4)
  }

  def addFive(i: Int) = {
    println("Add Five")
    i + 5
  }

  def addSix(i: Int) = {
    println("Add six")
    addThree(i) + addThree(i)
  }

  def addThree(i: Int) = {
    println("Add tree")
    i + 3
  }
}

