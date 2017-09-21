package io.kaitai.struct.languages

import io.kaitai.struct._
import io.kaitai.struct.datatype.DataType
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.exprlang.Ast.expr
import io.kaitai.struct.format._
import io.kaitai.struct.languages.components._
import io.kaitai.struct.translators.{CppTranslator, TypeDetector, TypeProvider}

object TypeUsage extends Enumeration {
  val Default, Undefined,
    InstanceDeclarationType, RootParentDeclarationType, AttributeDeclarationType, LocalVarType,
    ReturnType = Value
}

object CppStorageType extends Enumeration {
  val Undefined, Stack, ArrayOfScalar, RawPointer, UniquePointer = Value
}

class CppCompiler(
  typeProvider: ClassTypeProvider,
  config: RuntimeConfig
) extends LanguageCompiler(typeProvider, config)
    with ObjectOrientedLanguage
    with AllocateAndStoreIO
    with FixedContentsUsingArrayByteLiteral
    with UniversalDoc
    with EveryReadIsExpression {
  import CppCompiler._

  val outSrc = new StringLanguageOutputWriter(indent)
  val outHdr = new StringLanguageOutputWriter(indent)

  var identifierToNativeTypeTable = scala.collection.mutable.Map[Identifier,String]()

  def cppType(id: Identifier): String = {
    if (identifierToNativeTypeTable.contains(id)) {
      identifierToNativeTypeTable(id)
    } else {
      s"Undefined [id = ${id}]"
    }
  }

  def cppStorageType(cppType : String) : CppStorageType.Value = {
    if (isUniquePointerType(cppType)) {
      CppStorageType.UniquePointer
    } else if (isPointerType(cppType)){
      CppStorageType.RawPointer
    } else {
      CppStorageType.Stack
    }
  }

  def cppPointeeType(id : Identifier) : String = {
    val T = cppType(id)
    val ErrorMsg = "no_pointee_error"

    if (isUniquePointerType(T)) {
      val TemplateArgPattern = "<[a-zA-Z0-9_:]+>".r
      val Arg = TemplateArgPattern.findFirstIn(T).getOrElse(s"<$ErrorMsg>")
      Arg.substring(1,Arg.size-1)
    } else if (isPointerType(T)){
      s"*$T"
    } else {
      ErrorMsg
    }
  }

  def cppStorageType(id: Identifier) : CppStorageType.Value = cppStorageType(cppType(id))

  def storeIdentifierType(id: Identifier, cppType: String) : Unit = {
    identifierToNativeTypeTable += (id->cppType)
  }

  override def results(topClass: ClassSpec): Map[String, String] = {
    val fn = topClass.nameAsStr
    Map(
      s"$fn.cpp" -> outSrc.result,
      s"$fn.h" -> outHdr.result
    )
  }

  // helper function used in establishing whether pointers are owning
  def isRootOrParent(attrName: Identifier)  : Boolean = {
    (attrName == RootIdentifier) || (attrName == ParentIdentifier)
  }

  // helper function used in establishing whether a type is a pointer
  def isPointerType(typeString: String) : Boolean = {
    (typeString.trim().takeRight(1) ==  "*")
  }

  def isUniquePointerType(typeString: String) : Boolean = {
    typeString.trim().startsWith("std::unique_ptr")
  }

  override def getStatic = CppCompiler

  sealed trait AccessMode
  case object PrivateAccess extends AccessMode
  case object PublicAccess extends AccessMode

  var accessMode: AccessMode = PublicAccess

  override def indent: String = "    "
  override def outFileName(topClassName: String): String = topClassName

  override def fileHeader(topClassName: String): Unit = {
    outSrc.puts(s"// $headerComment")
    outSrc.puts
    outSrc.puts("#include \"" + outFileName(topClassName) + ".h\"")
    outSrc.puts
    outSrc.puts("#include <iostream>")
    outSrc.puts("#include <fstream>")

    outHdr.puts(s"#ifndef ${defineName(topClassName)}")
    outHdr.puts(s"#define ${defineName(topClassName)}")
    outHdr.puts
    outHdr.puts(s"// $headerComment")
    outHdr.puts
    outHdr.puts("#include <kaitai/kaitaistruct.h>")
    outHdr.puts("#include <kaitai/kaitaistream.h>")
    outHdr.puts
    outHdr.puts("#include <stdint.h>")
    outHdr.puts("#include <vector>") // TODO: add only if required
    outHdr.puts("#include <memory>") // TODO: add only if required
    outHdr.puts("#include <sstream>") // TODO: add only if required
    outHdr.puts("#include <algorithm>") // TODO: add only if required

    // API compatibility check
    val minVer = KSVersion.minimalRuntime.toInt
    outHdr.puts
    outHdr.puts(s"#if KAITAI_STRUCT_VERSION < ${minVer}L")
    outHdr.puts(
      "#error \"Incompatible Kaitai Struct C++/STL API: version " +
        KSVersion.minimalRuntime + " or later is required\""
    )
    outHdr.puts("#endif")
  }

  override def fileFooter(topClassName: String): Unit = {
    outHdr.puts
    outHdr.puts(s"#endif  // ${defineName(topClassName)}")
  }

  override def opaqueClassDeclaration(classSpec: ClassSpec): Unit = {
    classForwardDeclaration(classSpec.name)
    outSrc.puts("#include \"" + outFileName(classSpec.name.head) + ".h\"")
  }

  override def classHeader(name: List[String]): Unit = {
    outHdr.puts
    outHdr.puts(s"class ${types2class(List(name.last))} : public $kstructName {")
    outHdr.inc
    accessMode = PrivateAccess
    ensureMode(PublicAccess)

    /*
    outHdr.puts(s"static ${type2class(name)} from_file(std::string ${ReturnedTypeName("file_name")});")

    outSrc.puts
    outSrc.puts(s"${type2class(name)} ${type2class(name)}::from_file(std::string ${ReturnedTypeName("file_name")}) {")
    outSrc.inc
    outSrc.puts("std::ifstream* ifs = new std::ifstream(file_name, std::ifstream::binary);")
    outSrc.puts("kaitai::kstream *ks = new kaitai::kstream(ifs);")
    outSrc.puts(s"return new ${type2class(name)}(ks);")
    outSrc.dec
    outSrc.puts("}")
    */
  }

  override def classFooter(name: List[String]): Unit = {
    outHdr.dec
    outHdr.puts("};")
  }

  override def classForwardDeclaration(name: List[String]): Unit = {
    outHdr.puts(s"class ${types2class(name)};")
  }

  override def classConstructorHeader(name: List[String], parentClassName: List[String], rootClassName: List[String]): Unit = {
    outHdr.puts
    outHdr.puts(s"${types2class(List(name.last))}(" +
      s"$kstreamName* p_io, " +
      s"${types2class(parentClassName)}* p_parent = nullptr, " +
      s"${types2class(rootClassName)}* p_root = nullptr);"
    )

    outSrc.puts
    outSrc.puts(s"${types2class(name)}::${types2class(List(name.last))}(" +
      s"$kstreamName *p_io, " +
      s"${types2class(parentClassName)} *p_parent, " +
      s"${types2class(rootClassName)} *p_root) : $kstructName(p_io) {"
    )
    outSrc.inc
    handleAssignmentSimple(ParentIdentifier, "p_parent")
    handleAssignmentSimple(RootIdentifier, if (name == rootClassName) {
      "this"
    } else {
      "p_root"
    })
  }

  override def classConstructorFooter: Unit = {
    outSrc.dec
    outSrc.puts("}")
  }

  override def classDestructorHeader(name: List[String], parentTypeName: List[String], topClassName: List[String]): Unit = {
    outHdr.puts(s"~${types2class(List(name.last))}();")

    outSrc.puts
    outSrc.puts(s"${types2class(name)}::~${types2class(List(name.last))}() {")
    outSrc.inc
  }

  override def classDestructorFooter = classConstructorFooter

  override def storeAttributeType(attrName: Identifier, attrType: DataType, condSpec: ConditionalSpec): Unit = {
    if (isRootOrParent(attrName)) {
      val CppType = kaitaiType2NativeType(attrType, false, TypeUsage.RootParentDeclarationType)
      storeIdentifierType(attrName, CppType)
    } else {
      val CppType = kaitaiType2NativeType(attrType, false, TypeUsage.AttributeDeclarationType)
      storeIdentifierType(attrName, CppType)
    }
  }

  override def storeInstanceType(attrName: InstanceIdentifier, attrType: DataType, condSpec: ConditionalSpec): Unit = {
    val CppType = kaitaiType2NativeType(attrType,false, TypeUsage.InstanceDeclarationType)
    storeIdentifierType(attrName, CppType)
  }

  override def attributeDeclaration(attrName: Identifier, attrType: DataType, condSpec: ConditionalSpec): Unit = {
    ensureMode(PrivateAccess)
    var declaredType = cppType(attrName)
    outHdr.puts(s"${declaredType} ${privateMemberName(attrName)};")
    declareNullFlag(attrName, condSpec)
  }

  def ensureMode(newMode: AccessMode): Unit = {
    if (accessMode != newMode) {
      outHdr.dec
      outHdr.puts
      outHdr.puts(newMode match {
        case PrivateAccess => "private:"
        case PublicAccess => "public:"
      })
      outHdr.inc
      accessMode = newMode
    }
  }

  override def attributeReader(attrName: Identifier, attrType: DataType, condSpec: ConditionalSpec): Unit = {
    ensureMode(PublicAccess)
    val ReturnType = kaitaiType2NativeType(attrType,false,TypeUsage.ReturnType)
    if (isPointerType(ReturnType) && !(isRootOrParent(attrName))) {
      outHdr.puts(s"${ReturnType} ${publicMemberName(attrName)}() const { return ${privateMemberName(attrName)}.get(); }")
    } else {
      outHdr.puts(s"${ReturnType} ${publicMemberName(attrName)}() const { return ${privateMemberName(attrName)}; }")
    }
  }

  override def universalDoc(doc: DocSpec): Unit = {
    // All docstrings would be for public stuff, so it's safe to start it here
    ensureMode(PublicAccess)

    outHdr.puts
    outHdr.puts( "/**")

    doc.summary.foreach((docStr) => outHdr.putsLines(" * ", docStr))

    doc.ref match {
      case TextRef(text) =>
        outHdr.putsLines(" * ", s"\\sa $text")
      case UrlRef(url, text) =>
        outHdr.putsLines(" * ", s"\\sa $text")
      case NoRef =>
        // nothing to output
    }

    outHdr.puts( " */")
  }

  override def attrDestructor(attr: AttrLikeSpec, id: Identifier): Unit = {
    val t = attr.dataTypeComposite

    val checkFlags = attr match {
      case is: InstanceSpec =>
        val dataType = is.dataTypeComposite
        dataType match {
          case ut: UserType =>
            val checkLazy = calculatedFlagForName(id.asInstanceOf[InstanceIdentifier])
            val checkNull = if (is.cond.ifExpr.isDefined) {
              s" && !${nullFlagForName(id)}"
            } else {
              ""
            }
            outSrc.puts(s"if ($checkLazy$checkNull) {")
            outSrc.inc
            true
          case _ =>
            false
        }
      case as: AttrSpec =>
        as.dataType match {
          case ut: UserType =>
            if (as.cond.ifExpr.isDefined) {
              outSrc.puts(s"if (!${nullFlagForName(id)}) {")
              outSrc.inc
              true
            } else {
              false
            }
          case _ =>
            false
        }
    }

//    t match {
//      case ArrayType(_: UserTypeFromBytes) =>
//        outSrc.puts(s"delete ${privateMemberName(RawIdentifier(id))};")
//      case _ =>
//        // no cleanup needed
//    }

//    t match {
//      case ArrayType(el: UserType) =>
//        val arrVar = privateMemberName(id)
//        outSrc.puts(s"for (std::vector<${kaitaiType2NativeType(el)}>::iterator it = $arrVar->begin(); it != $arrVar->end(); ++it) {")
//        outSrc.inc
//        outSrc.puts("delete *it;")
//        outSrc.dec
//        outSrc.puts("}")
//      case _ =>
//        // no cleanup needed
//    }

//    t match {
//      case _: UserTypeFromBytes =>
//        outSrc.puts(s"delete ${privateMemberName(IoStorageIdentifier(RawIdentifier(id)))};")
//      case _ =>
//        // no cleanup needed
//    }

//    t match {
//      case _: UserType | _: ArrayType =>
//        outSrc.puts(s"delete ${privateMemberName(id)};")
//      case _ =>
//        // no cleanup needed
//    }

    if (checkFlags) {
      outSrc.dec
      outSrc.puts("}")
    }
  }

  override def attrFixedContentsParse(attrName: Identifier, contents: String): Unit = {
    outSrc.puts(s"${privateMemberName(attrName)} = $normalIO->ensure_fixed_contents($contents);")
  }

  override def attrProcess(proc: ProcessExpr, varSrc: Identifier, varDest: Identifier): Unit = {
    val srcName = privateMemberName(varSrc)
    val destName = privateMemberName(varDest)

    proc match {
      case ProcessXor(xorValue) =>
        val procName = translator.detectType(xorValue) match {
          case _: IntType => "process_xor_one"
          case _: BytesType => "process_xor_many"
        }
        outSrc.puts(s"$destName = $kstreamName::$procName($srcName, ${expression(xorValue)});")
      case ProcessZlib =>
        outSrc.puts(s"$destName = $kstreamName::process_zlib($srcName);")
      case ProcessRotate(isLeft, rotValue) =>
        val expr = if (isLeft) {
          expression(rotValue)
        } else {
          s"8 - (${expression(rotValue)})"
        }
        outSrc.puts(s"$destName = $kstreamName::process_rotate_left($srcName, $expr);")
    }
  }

  override def allocateIO(varName: Identifier, rep: RepeatSpec): IoStorageIdentifier = {
    val memberName = privateMemberName(varName)

    val ioName = IoStorageIdentifier(varName)

    val args = rep match {
      case RepeatEos | RepeatExpr(_) => s"$memberName->at($memberName->size() - 1)"
      case RepeatUntil(_) => translator.doName(Identifier.ITERATOR2)
      case NoRepeat => memberName
    }

    outSrc.puts(s"${privateMemberName(ioName)} = std::make_unique<$kstreamName>($args);")
    ioName
  }

  override def useIO(ioEx: Ast.expr): String = {
    outSrc.puts(s"$kstreamName *io = ${expression(ioEx)};")
    "io"
  }

  override def pushPos(io: String): Unit =
    outSrc.puts(s"std::streampos _pos = $io->pos();")

  override def seek(io: String, pos: Ast.expr): Unit =
    outSrc.puts(s"$io->seek(${expression(pos)});")

  override def popPos(io: String): Unit =
    outSrc.puts(s"$io->seek(_pos);")

  override def alignToByte(io: String): Unit =
    outSrc.puts(s"$io->align_to_byte();")

  override def instanceClear(instName: InstanceIdentifier): Unit = {
    outSrc.puts(s"${calculatedFlagForName(instName)} = false;")
  }

  override def instanceSetCalculated(instName: InstanceIdentifier): Unit = {
    outSrc.puts(s"${calculatedFlagForName(instName)} = true;")
  }

  override def condIfSetNull(instName: Identifier): Unit =
    outSrc.puts(s"${nullFlagForName(instName)} = true;")

  override def condIfSetNonNull(instName: Identifier): Unit =
    outSrc.puts(s"${nullFlagForName(instName)} = false;")

  override def condIfHeader(expr: Ast.expr): Unit = {
    outSrc.puts(s"if (${expression(expr)}) {")
    outSrc.inc
  }

  override def condIfFooter(expr: Ast.expr): Unit = {
    outSrc.dec
    outSrc.puts("}")
  }

  override def condRepeatEosHeader(id: Identifier, io: String, dataType: DataType, needRaw: Boolean): Unit = {
    if (needRaw) {
      outSrc.puts(s"${privateMemberName(RawIdentifier(id))} = std::make_unique<std::string>();")
    }
    val CppInnerType = kaitaiType2NativeType(dataType,false,TypeUsage.InstanceDeclarationType)
    outSrc.puts(s"${privateMemberName(id)} = std::make_unique<std::vector<$CppInnerType>>();")
    outSrc.puts(s"while (!$io->is_eof()) {")
    outSrc.inc
  }

  override def handleAssignmentRepeatEos(id: Identifier, expr: String): Unit = {
    outSrc.puts(s"${privateMemberName(id)}->push_back($expr);")
  }

  override def condRepeatEosFooter: Unit = {
    outSrc.dec
    outSrc.puts("}")
  }

  override def condRepeatExprHeader(id: Identifier, io: String, dataType: DataType, needRaw: Boolean, repeatExpr: Ast.expr): Unit = {
    val lenVar = s"l_${idToStr(id)}"
    outSrc.puts(s"int $lenVar = ${expression(repeatExpr)};")
    if (needRaw) {
      outSrc.puts(s"${privateMemberName(RawIdentifier(id))} = std::make_unique<std::vector<std::string>>();")
      outSrc.puts(s"${privateMemberName(RawIdentifier(id))}->reserve($lenVar);")
    }
    val CppInnerType = kaitaiType2NativeType(dataType,false,TypeUsage.InstanceDeclarationType)
    outSrc.puts(s"${privateMemberName(id)} = std::make_unique<std::vector<$CppInnerType>>();");
    outSrc.puts(s"${privateMemberName(id)}->reserve($lenVar);")
    outSrc.puts(s"for (int i = 0; i < $lenVar; i++) {")
    outSrc.inc
  }

  override def handleAssignmentRepeatExpr(id: Identifier, expr: String): Unit = {
    outSrc.puts(s"${privateMemberName(id)}->push_back($expr);")
  }

  override def condRepeatExprFooter: Unit = {
    outSrc.dec
    outSrc.puts("}")
  }

  override def condRepeatUntilHeader(id: Identifier, io: String, dataType: DataType, needRaw: Boolean, untilExpr: expr): Unit = {
    if (needRaw) {
      outSrc.puts(s"${privateMemberName(RawIdentifier(id))} = std::make_unique<std::vector<std::string>>();")
    }

    var CppInnerType = kaitaiType2NativeType(dataType,false,TypeUsage.InstanceDeclarationType)

    outSrc.puts(s"${privateMemberName(id)} = std::make_unique<std::vector<$CppInnerType>>();")
    outSrc.puts("{")
    outSrc.inc

    val CppLocalType = kaitaiType2NativeType(dataType,false,TypeUsage.LocalVarType)

    outSrc.puts(s"$CppLocalType ${translator.doName("_")};") // allocates local variable
    outSrc.puts("do {")
    outSrc.inc
  }

  override def handleAssignmentRepeatUntil(id: Identifier, expr: String, isRaw: Boolean): Unit = {
    val (typeDecl, tempVar) = if (isRaw) {
      ("std::string ", translator.doName(Identifier.ITERATOR2))
    } else {
      ("", translator.doName(Identifier.ITERATOR))
    }

    if (isRaw) {
      outSrc.puts(s"$typeDecl$tempVar = $expr;")
      outSrc.puts(s"${privateMemberName(id)}->push_back($tempVar);")
    } else {
      outSrc.puts(s"${privateMemberName(id)}->push_back($expr);")

      // Note: cppStorageType(id) is not yet useable
      if (expr.startsWith("std::make_unique")) {
        outSrc.puts(s"$tempVar = ${privateMemberName(id)}->back().get();")
      } else {
        outSrc.puts(s"$tempVar = ${privateMemberName(id)}->back();")
      }
    }
  }

  override def condRepeatUntilFooter(id: Identifier, io: String, dataType: DataType, needRaw: Boolean, untilExpr: expr): Unit = {
    typeProvider._currentIteratorType = Some(dataType)
    outSrc.dec
    outSrc.puts(s"} while (!(${expression(untilExpr)}));")
    outSrc.dec
    outSrc.puts("}")
  }

  override def handleAssignmentSimple(id: Identifier, expr: String): Unit = {
    val MemberId = privateMemberName(id)

    if (expr.startsWith("std::make_unique") ||  (cppStorageType(id) != CppStorageType.UniquePointer)) {
      outSrc.puts(s"$MemberId = $expr;")
    } else {
      outSrc.puts(s"$MemberId = std::make_unique<${cppPointeeType(id)}>(*$expr);")
    }
  }

  override def parseExpr(dataType: DataType, io: String): String = {
    dataType match {
      case t: ReadableType =>
        s"$io->read_${t.apiCall}()"
      case blt: BytesLimitType =>
        s"$io->read_bytes(${expression(blt.size)})"
      case _: BytesEosType =>
        s"$io->read_bytes_full()"
      case BytesTerminatedType(terminator, include, consume, eosError, _) =>
        s"$io->read_bytes_term($terminator, $include, $consume, $eosError)"
      case BitsType1 =>
        s"$io->read_bits_int(1)"
      case BitsType(width: Int) =>
        s"$io->read_bits_int($width)"
      case t: UserType =>
        val addArgs = if (t.isOpaque) {
          ""
        } else {
          val parent = t.forcedParent match {
            case Some(USER_TYPE_NO_PARENT) => "nullptr"
            case Some(fp) => {
              translator.translate(fp)
            }
            case None => "this"
          }
          s", $parent, ${privateMemberName(RootIdentifier)}"
        }
        // PBO: UserTypeInstream-s are always 'owned pointers'
        // This works with the current set of unit tests but
        //  this test might need to be generalized
        if (t.isInstanceOf[UserTypeInstream]) {
          s"std::make_unique<${types2class(t.name)}>($io$addArgs) /* io: $io */"
        } else {
          //
          s"std::make_unique<${types2class(t.name)}>($io.get()$addArgs) /* io: $io */"
        }
    }
  }

  override def bytesPadTermExpr(expr0: String, padRight: Option[Int], terminator: Option[Int], include: Boolean) = {
    val expr1 = padRight match {
      case Some(padByte) => s"$kstreamName::bytes_strip_right($expr0, $padByte)"
      case None => expr0
    }
    val expr2 = terminator match {
      case Some(term) => s"$kstreamName::bytes_terminate($expr1, $term, $include)"
      case None => expr1
    }
    expr2
  }

  /**
    * Designates switch mode. If false, we're doing real switch-case for this
    * attribute. If true, we're doing if-based emulation.
    */
  var switchIfs = false

  override def switchStart(id: Identifier, on: Ast.expr): Unit = {
    val onType = translator.detectType(on)

    // Determine switching mode for this construct based on type
    switchIfs = onType match {
      case _: IntType | _: EnumType => false
      case _ => true
    }

    if (switchIfs) {
      outSrc.puts("{")
      outSrc.inc
      // PBO: the way the type is used is set to default, which at least works with
      // the current set of unit tests
      outSrc.puts(s"${kaitaiType2NativeType(onType,false,TypeUsage.Default)} on = ${expression(on)};")
    } else {
      outSrc.puts(s"switch (${expression(on)}) {")
    }
  }

  override def switchCaseFirstStart(condition: Ast.expr): Unit = {
    if (switchIfs) {
      outSrc.puts(s"if (on == ${expression(condition)}) {")
      outSrc.inc
    } else {
      outSrc.puts(s"case ${expression(condition)}:")
      outSrc.inc
    }
  }

  override def switchCaseStart(condition: Ast.expr): Unit = {
    if (switchIfs) {
      outSrc.puts(s"else if (on == ${expression(condition)}) {")
      outSrc.inc
    } else {
      outSrc.puts(s"case ${expression(condition)}:")
      outSrc.inc
    }
  }

  override def switchCaseEnd(): Unit = {
    if (switchIfs) {
      outSrc.dec
      outSrc.puts("}")
    } else {
      outSrc.puts("break;")
      outSrc.dec
    }
  }

  override def switchElseStart(): Unit = {
    if (switchIfs) {
      outSrc.puts("else {")
      outSrc.inc
    } else {
      outSrc.puts("default:")
      outSrc.inc
    }
  }

  override def switchEnd(): Unit =
    if (switchIfs) {
      outSrc.dec
      outSrc.puts("}")
    } else {
      outSrc.puts("}")
    }

  override def switchBytesOnlyAsRaw = true

  override def instanceDeclaration(attrName: InstanceIdentifier, attrType: DataType, condSpec: ConditionalSpec): Unit = {
    ensureMode(PrivateAccess)
    var declaredType = kaitaiType2NativeType(attrType,false, TypeUsage.InstanceDeclarationType)
    outHdr.puts(s"bool ${calculatedFlagForName(attrName)};")
    outHdr.puts(s"${declaredType} ${privateMemberName(attrName)};")
    declareNullFlag(attrName, condSpec)
  }

  override def instanceHeader(className: List[String], instName: InstanceIdentifier, dataType: DataType): Unit = {
    ensureMode(PublicAccess)
    outHdr.puts(s"${kaitaiType2NativeType(dataType,absolute = false,TypeUsage.ReturnType)} ${publicMemberName(instName)}();")
    outSrc.puts
    outSrc.puts(s"${kaitaiType2NativeType(dataType,true, TypeUsage.ReturnType)} ${types2class(className)}::${publicMemberName(instName)}() {")
    outSrc.inc
  }

  override def instanceFooter: Unit = {
    outSrc.dec
    outSrc.puts("}")
  }

  override def instanceCheckCacheAndReturn(instName: InstanceIdentifier, dataType: DataType): Unit = {
    outSrc.puts(s"if (${calculatedFlagForName(instName)}) {")
    outSrc.inc
    instanceReturn(instName, dataType)
    outSrc.dec
    outSrc.puts(s"}"
    )
  }

  override def instanceReturn(instName: InstanceIdentifier, dataType: DataType): Unit = {
    val ReturnType = kaitaiType2NativeType(dataType, true, TypeUsage.ReturnType);
    if (isPointerType(ReturnType)) {
      outSrc.puts(s"return ${privateMemberName(instName)}.get();")
    } else {
      outSrc.puts(s"return ${privateMemberName(instName)};")
    }
  }

  override def enumDeclaration(curClass: List[String], enumName: String, enumColl: Seq[(Long, String)]): Unit = {
    val enumClass = types2class(List(enumName))

    outHdr.puts
    outHdr.puts(s"enum $enumClass {")
    outHdr.inc

    if (enumColl.size > 1) {
      enumColl.dropRight(1).foreach { case (id, label) =>
        outHdr.puts(s"${value2Const(enumName, label)} = $id,")
      }
    }
    enumColl.last match {
      case (id, label) =>
        outHdr.puts(s"${value2Const(enumName, label)} = $id")
    }

    outHdr.dec
    outHdr.puts("};")
  }

  def value2Const(enumName: String, label: String) = (enumName + "_" + label).toUpperCase

  def defineName(className: String) = className.toUpperCase + "_H_"

  def calculatedFlagForName(ksName: InstanceIdentifier) =
    s"f_${ksName.name}"

  def nullFlagForName(ksName: Identifier) = {
    ksName match {
      case NamedIdentifier(name) => s"n_$name"
      case InstanceIdentifier(name) => s"n_$name"
    }
  }

  override def idToStr(id: Identifier): String = {
    id match {
      case RawIdentifier(inner) => s"_raw_${idToStr(inner)}"
      case IoStorageIdentifier(inner) => s"_io_${idToStr(inner)}"
      case si: SpecialIdentifier => si.name
      case ni: NamedIdentifier => ni.name
      case NumberedIdentifier(idx) => s"_${NumberedIdentifier.TEMPLATE}$idx"
      case ni: InstanceIdentifier => ni.name
    }
  }

  override def privateMemberName(id: Identifier): String = s"m_${idToStr(id)}"

  override def publicMemberName(id: Identifier): String = idToStr(id)

  def declareNullFlag(attrName: Identifier, condSpec: ConditionalSpec) = {
    if (condSpec.ifExpr.nonEmpty) {
      outHdr.puts(s"bool ${nullFlagForName(attrName)};")
      ensureMode(PublicAccess)
      outHdr.puts(s"bool _is_null_${idToStr(attrName)}() { ${publicMemberName(attrName)}(); return ${nullFlagForName(attrName)}; };")
      ensureMode(PrivateAccess)
    }
  }

  def type2class(name: String) = name + "_t"
}

object CppCompiler extends LanguageCompilerStatic with StreamStructNames {
  override def getTranslator(tp: TypeProvider, config: RuntimeConfig) = new CppTranslator(tp)
  override def getCompiler(
    tp: ClassTypeProvider,
    config: RuntimeConfig
  ): LanguageCompiler = new CppCompiler(tp, config)

  val kNameSpace = "kaitai"
  override def kstructName = kNameSpace + "::kstruct"
  override def kstreamName = kNameSpace + "::kstream"

  def types2class(components: List[String]) = {
    components.map {
      case "kaitai_struct" => kNameSpace + "::kstruct"
      case s => s + "_t"
    }.mkString("::")
  }

  def kaitaiType2NativeType(attrType: DataType, absolute: Boolean = false, typeUse: TypeUsage.Value = TypeUsage.Default): String = {

    attrType match {

      case Int1Type(false) => "uint8_t"
      case IntMultiType(false, Width2, _) => "uint16_t"
      case IntMultiType(false, Width4, _) => "uint32_t"
      case IntMultiType(false, Width8, _) => "uint64_t"
      case IntMultiType(false, _, _) => "uint64_t"

      case Int1Type(true) => "int8_t"
      case IntMultiType(true, Width2, _) => "int16_t"
      case IntMultiType(true, Width4, _) => "int32_t"
      case IntMultiType(true, Width8, _) => "int64_t"
      case IntMultiType(true, _, _) => "int64_t"

      case FloatMultiType(Width4, _) => "float"
      case FloatMultiType(Width8, _) => "double"

      case BitsType(_) => "uint64_t"

      case _: BooleanType => "bool"
      case CalcIntType => "int32_t"
      case CalcFloatType => "double"

      case _: StrType => "std::string"
      case _: BytesType => "std::string"

      case t: UserType =>
        val typeStr = types2class(if (absolute) {
          t.classSpec.get.name
        } else {
          t.name
        })
        if ((typeUse == TypeUsage.InstanceDeclarationType) || (typeUse == TypeUsage.AttributeDeclarationType)) {
          s"std::unique_ptr<$typeStr>"
        } else {
          s"$typeStr*"
        }

      case t: EnumType =>
        types2class(if (absolute) {
          t.enumSpec.get.name
        } else {
          t.name
        })

      case ArrayType(inType) =>
        if (typeUse == TypeUsage.ReturnType) {
          s"std::vector<${kaitaiType2NativeType(inType, absolute, TypeUsage.InstanceDeclarationType)}>*"
        } else {
          s"std::unique_ptr<std::vector<${kaitaiType2NativeType(inType, absolute, typeUse)}>>"
        }

      case KaitaiStreamType =>
       if (typeUse == TypeUsage.ReturnType) {
         s"$kstreamName*"
       } else {
          s"std::unique_ptr<$kstreamName>"
        }

      case KaitaiStructType =>
        if (typeUse == TypeUsage.ReturnType) {
          s"$kstructName*"
        } else {
          s"std::unique_ptr<$kstructName>"
        }

      case SwitchType(on, cases) =>
        kaitaiType2NativeType(TypeDetector.combineTypes(
          // C++ does not have a concept of AnyType, and common use case "lots of incompatible UserTypes
          // for cases + 1 BytesType for else" combined would result in exactly AnyType - so we try extra
          // hard to avoid that here with this pre-filtering. In C++, "else" case with raw byte array would
          // be available through _raw_* attribute anyway.
          cases.filterNot { case (caseExpr, caseValue) => caseExpr == SwitchType.ELSE_CONST }.values
        ), absolute,typeUse)

      case _ => throw new RuntimeException(s"kaitaiType2NativeType could not deduce native type for ${attrType}")
    }
  }
}
