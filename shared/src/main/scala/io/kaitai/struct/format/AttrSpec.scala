package io.kaitai.struct.format

import java.nio.charset.Charset

import io.kaitai.struct.Utils
import io.kaitai.struct.datatype.DataType
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.exprlang.Ast.expr
import io.kaitai.struct.exprlang.{Ast, Expressions}

import scala.collection.JavaConversions._

sealed trait RepeatSpec
case class RepeatExpr(expr: Ast.expr) extends RepeatSpec
case class RepeatUntil(expr: Ast.expr) extends RepeatSpec
case object RepeatEos extends RepeatSpec
case object NoRepeat extends RepeatSpec

case class ConditionalSpec(ifExpr: Option[Ast.expr], repeat: RepeatSpec)

trait AttrLikeSpec extends YAMLPath {
  def dataType: DataType
  def cond: ConditionalSpec
  def doc: DocSpec

  def isArray: Boolean = cond.repeat != NoRepeat

  def dataTypeComposite: DataType = {
    if (isArray) {
      ArrayType(dataType)
    } else {
      dataType
    }
  }
}

case class AttrSpec(
  path: List[String],
  id: Identifier,
  dataType: DataType,
  cond: ConditionalSpec = ConditionalSpec(None, NoRepeat),
  doc: DocSpec = DocSpec.EMPTY
) extends AttrLikeSpec

case class YamlAttrArgs(
  size: Option[Ast.expr],
  sizeEos: Boolean,
  encoding: Option[String],
  terminator: Option[Int],
  include: Boolean,
  consume: Boolean,
  eosError: Boolean,
  padRight: Option[Int],
  contents: Option[Array[Byte]],
  enumRef: Option[String],
  parent: Option[Ast.expr],
  process: Option[ProcessExpr]
) {
  def getByteArrayType(path: List[String]) = {
    (size, sizeEos) match {
      case (Some(bs: expr), false) =>
        BytesLimitType(bs, terminator, include, padRight, process)
      case (None, true) =>
        BytesEosType(terminator, include, padRight, process)
      case (None, false) =>
        terminator match {
          case Some(term) =>
            BytesTerminatedType(term, include, consume, eosError, process)
          case None =>
            throw new YAMLParseException("'size', 'size-eos' or 'terminator' must be specified", path)
        }
      case (Some(_), true) =>
        throw new YAMLParseException("only one of 'size' or 'size-eos' must be specified", path)
    }
  }
}

object AttrSpec {
  val LEGAL_KEYS = Set(
    "id",
    "doc",
    "doc-ref",
    "type",
    "if",
    "terminator",
    "consume",
    "include",
    "eos-error",
    "repeat"
  )

  val LEGAL_KEYS_BYTES = Set(
    "contents",
    "size",
    "size-eos",
    "pad-right",
    "parent",
    "process"
  )

  val LEGAL_KEYS_STR = Set(
    "size",
    "size-eos",
    "pad-right",
    "encoding"
  )

  val LEGAL_KEYS_ENUM = Set(
    "enum"
  )

  def fromYaml(src: Any, path: List[String], metaDef: MetaDefaults, idx: Int): AttrSpec = {
    val srcMap = ParseUtils.asMapStr(src, path)
    val id = ParseUtils.getOptValueStr(srcMap, "id", path) match {
      case Some(idStr) =>
        try {
          NamedIdentifier(idStr)
        } catch {
          case _: InvalidIdentifier =>
            throw YAMLParseException.invalidId(idStr, "attribute", path ++ List("id"))
        }
      case None => NumberedIdentifier(idx)
    }
    fromYaml(srcMap, path, metaDef, id)
  }

  def fromYaml(srcMap: Map[String, Any], path: List[String], metaDef: MetaDefaults, id: Identifier): AttrSpec = {
    try {
      fromYaml2(srcMap, path, metaDef, id)
    } catch {
      case (epe: Expressions.ParseException) =>
        throw YAMLParseException.expression(epe, path)
    }
  }

  def fromYaml2(srcMap: Map[String, Any], path: List[String], metaDef: MetaDefaults, id: Identifier): AttrSpec = {
    val doc = DocSpec.fromYaml(srcMap, path)
    val process = ProcessExpr.fromStr(ParseUtils.getOptValueStr(srcMap, "process", path))
    // TODO: add proper path propagation
    val contents = srcMap.get("contents").map(parseContentSpec(_, path ++ List("contents")))
    val size = ParseUtils.getOptValueStr(srcMap, "size", path).map(Expressions.parse)
    val sizeEos = ParseUtils.getOptValueBool(srcMap, "size-eos", path).getOrElse(false)
    val ifExpr = ParseUtils.getOptValueStr(srcMap, "if", path).map(Expressions.parse)
    val encoding = ParseUtils.getOptValueStr(srcMap, "encoding", path)
    val repeat = ParseUtils.getOptValueStr(srcMap, "repeat", path)
    val repeatExpr = ParseUtils.getOptValueStr(srcMap, "repeat-expr", path).map(Expressions.parse)
    val repeatUntil = ParseUtils.getOptValueStr(srcMap, "repeat-until", path).map(Expressions.parse)
    val terminator = ParseUtils.getOptValueInt(srcMap, "terminator", path)
    val consume = ParseUtils.getOptValueBool(srcMap, "consume", path).getOrElse(true)
    val include = ParseUtils.getOptValueBool(srcMap, "include", path).getOrElse(false)
    val eosError = ParseUtils.getOptValueBool(srcMap, "eos-error", path).getOrElse(true)
    val padRight = ParseUtils.getOptValueInt(srcMap, "pad-right", path)
    val enum = ParseUtils.getOptValueStr(srcMap, "enum", path)
    val parent = ParseUtils.getOptValueStr(srcMap, "parent", path).map(Expressions.parse)

    val typObj = srcMap.get("type")

    val yamlAttrArgs = YamlAttrArgs(
      size, sizeEos,
      encoding, terminator, include, consume, eosError, padRight,
      contents, enum, parent, process
    )

    // Unfortunately, this monstrous match can't rewritten in simpler way due to Java type erasure
    val dataType: DataType = typObj match {
      case None =>
        DataType.fromYaml(
          None, path, metaDef, yamlAttrArgs
        )
      case Some(x) =>
        x match {
          case simpleType: String =>
            DataType.fromYaml(
              Some(simpleType), path, metaDef, yamlAttrArgs
            )
          case switchMap: Map[Any, Any] =>
            val switchMapStr = ParseUtils.anyMapToStrMap(switchMap, path)
            parseSwitch(switchMapStr, path, metaDef, yamlAttrArgs)
          case unknown =>
            throw new YAMLParseException(s"expected map or string, found $unknown", path ++ List("type"))
        }
    }

    val (repeatSpec, legalRepeatKeys) = parseRepeat(repeat, repeatExpr, repeatUntil, path)

    val legalKeys = LEGAL_KEYS ++ legalRepeatKeys ++ (dataType match {
      case _: BytesType => LEGAL_KEYS_BYTES
      case _: StrFromBytesType => LEGAL_KEYS_STR
      case _: UserType => LEGAL_KEYS_BYTES
      case EnumType(_, _) => LEGAL_KEYS_ENUM
      case SwitchType(on, cases) => LEGAL_KEYS_BYTES
      case _ => Set()
    })

    ParseUtils.ensureLegalKeys(srcMap, legalKeys, path)

    AttrSpec(path, id, dataType, ConditionalSpec(ifExpr, repeatSpec), doc)
  }

  def parseContentSpec(c: Any, path: List[String]): Array[Byte] = {
    c match {
      case s: String =>
        s.getBytes(Charset.forName("UTF-8"))
      case objects: List[_] =>
        val bb = new scala.collection.mutable.ArrayBuffer[Byte]
        objects.zipWithIndex.foreach { case (value, idx) =>
          value match {
            case s: String =>
              bb.appendAll(Utils.strToBytes(s))
            case integer: Integer =>
              bb.append(Utils.clampIntToByte(integer))
            case el =>
              throw new YAMLParseException(s"unable to parse fixed content in array: $el", path ++ List(idx.toString))
          }
        }
        bb.toArray
      case _ =>
        throw new YAMLParseException(s"unable to parse fixed content: $c", path)
    }
  }

  val LEGAL_KEYS_SWITCH = Set(
    "switch-on",
    "cases"
  )

  private def parseSwitch(
    switchSpec: Map[String, Any],
    path: List[String],
    metaDef: MetaDefaults,
    arg: YamlAttrArgs
  ): DataType = {
    val _on = ParseUtils.getValueStr(switchSpec, "switch-on", path)
    val _cases: Map[String, String] = switchSpec.get("cases") match {
      case None => Map()
      case Some(x) => ParseUtils.asMapStrStr(x, path ++ List("cases"))
    }

    ParseUtils.ensureLegalKeys(switchSpec, LEGAL_KEYS_SWITCH, path)

    val on = Expressions.parse(_on)
    val cases = _cases.map { case (condition, typeName) =>
      Expressions.parse(condition) -> DataType.fromYaml(
        Some(typeName), path ++ List("cases"), metaDef,
        arg
      )
    }

    // If we have size defined, and we don't have any "else" case already, add
    // an implicit "else" case that will at least catch everything else as
    // "untyped" byte array of given size
    val addCases: Map[Ast.expr, DataType] = if (cases.containsKey(SwitchType.ELSE_CONST)) {
      Map()
    } else {
      (arg.size, arg.sizeEos) match {
        case (Some(sizeValue), false) =>
          Map(SwitchType.ELSE_CONST -> BytesLimitType(sizeValue, None, false, None, arg.process))
        case (None, true) =>
          Map(SwitchType.ELSE_CONST -> BytesEosType(None, false, None, arg.process))
        case (None, false) =>
          Map()
        case (Some(_), true) =>
          throw new YAMLParseException("can't have both `size` and `size-eos` defined", path)
      }
    }

    SwitchType(on, cases ++ addCases)
  }

  private def parseRepeat(
    repeat: Option[String],
    rExpr: Option[Ast.expr],
    rUntil: Option[Ast.expr],
    path: List[String]
  ): (RepeatSpec, Set[String]) = {
    repeat match {
      case None =>
        (NoRepeat, Set())
      case Some("until") =>
        val spec = rUntil match {
          case Some(expr) => RepeatUntil(expr)
          case None =>
            throw new YAMLParseException(
              "`repeat: until` requires a `repeat-until` expression",
              path ++ List("repeat")
            )
        }
        (spec, Set("repeat-until"))
      case Some("expr") =>
        val spec = rExpr match {
          case Some(expr) => RepeatExpr(expr)
          case None =>
            throw new YAMLParseException(
              "`repeat: expr` requires a `repeat-expr` expression",
              path ++ List("repeat")
            )
        }
        (spec, Set("repeat-expr"))
      case Some("eos") =>
        (RepeatEos, Set())
      case Some(other) =>
        throw YAMLParseException.badDictValue(
          Set("until", "expr", "eos"), other, path ++ List("repeat")
        )
    }
  }
}
