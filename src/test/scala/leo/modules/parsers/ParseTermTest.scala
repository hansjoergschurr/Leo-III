package leo.modules.parsers

import leo.modules.parsers.utils.GenerateTerm
import leo.modules.parsers.syntactical.{TPTPParsers => TermParser0}
import leo.modules.parsers.syntactical_new.termParser_functional.{TermParser => TermParserFunctional}
import leo.modules.parsers.syntactical_new.termParser2.TermParser2
import leo.{Checked, Ignored, LeoTestSuite}
import leo.datastructures.tptp.Commons._

import scala.util.parsing.input.Position

//import leo.modules.parsers.syntactical_new.termParser._

//import leo.modules.parsers.lexical.TPTPLexical

/**
  * Created by samuel on 08.03.16.
  */
class ParseTermTest
  extends LeoTestSuite
{

  test("testTermGen", Ignored) {
    //println(s"sq_char: ${sq_char}")
    //println(s"do_char: ${do_char}")
    for( length <- 10 to 100 ) {
      val term = utils.GenerateTerm(length)
      assert( length == term.length)
      //println( s"length: ${length}, real: ${term.length}; ${term}" )
    }
  }

  def testParser(parser: ParserInterface[Term]): Unit = {

    def tokensToString(tokStream: Seq[parser.Token]): String = {
      tokStream map {
        case parser.lexical.SingleQuoted(x) => x
        case x => x.chars
      } reduce (_+_)
    }

    for{
    //_ <- 0 to 100
      length <- 10 to 500 by 10
    } {

      val term = GenerateTerm(length)
      println(s"length: ${length}, parsing term: ${term}")
      val tokStream = parser.tokenize(term)
      //println(s"tokens: ${tokStream}")

      val parseRet = parser.parse(tokStream)
      parseRet match {
        case Left(err)
        => fail(s"parser failed! error message: ${err}")
        case Right((syntaxTree, inputRest))
        =>
          //println(s"parser returned: ${syntaxTree}, rest: ${inputRest}")
          assert( syntaxTree.toString == tokensToString(tokStream) )
          assert( inputRest == Nil )
      }
    }
  }

  object TermParser0Wrapper
    extends ParserInterface[Term]
  {
    override val lexical = TermParser0.lexical
    type Token = TermParser0.lexical.Token

    def tokenize(input: String): Seq[Token] = {
      var scanner = new TermParser0.lexical.Scanner(input)
      var tokStream: Seq[Token] = List[Token]()
      while(!scanner.atEnd) {
        tokStream = tokStream :+ scanner.first
        scanner = scanner.rest
      }
      tokStream
    }
    def parse(input: String): Either[String,(Term, Seq[Token])] = {
      TermParser0.parse(input, TermParser0.term) match {
        case TermParser0.Success(x,rest) => Right((x, Seq()))
        case _ => Left("parser failed!")
      }
    }
    def parse(input: Seq[Token]): Either[String,(Term, Seq[Token])] = {
      import util.parsing.input.Reader
      class TokenReader(data: Seq[Token])
        extends Reader[Token]
      {
        override def first: Token =
          data.head
        override def atEnd: Boolean =
          data.isEmpty
        override def pos: Position =
          new Position{ def lineContents = "<>"; def line = 0; def column = 0 }
        override def rest: Reader[Token] =
          new TokenReader(data.tail)
      }
      TermParser0.term(new TokenReader(input)) match {
        case TermParser0.Success(x,rest) => Right((x, Seq()))
        case _ => Left("parser failed!")
      }
    }
  }

  test("original parser (based on scala parser combinators):", Checked) {
    testParser(TermParser0Wrapper)
  }
  test("new functional TermParser", Checked) {
    testParser(TermParserFunctional)
  }
  test("new TermParser", Checked) {
    testParser(TermParser2)
  }

  /*
  test("testUntypedParsing", Checked) {
    //println("parser 0")
    //testParser(TermParser0Wrapper)
    println("parser 1")
    testParser(TermParserFunctional)
    println("parser 2")
    testParser(TermParser2)
  }
  */
}
