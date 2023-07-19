// Generated from /run/media/mmcblk0p1/Sireum/logika/jvm/src/main/scala/org/sireum/logika/SMTLIBv2.g4 by ANTLR 4.12.0
package org.sireum.logika.modelparser;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link SMTLIBv2Parser}.
 */
public interface SMTLIBv2Listener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void enterStart(SMTLIBv2Parser.StartContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#start}.
	 * @param ctx the parse tree
	 */
	void exitStart(SMTLIBv2Parser.StartContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#response}.
	 * @param ctx the parse tree
	 */
	void enterResponse(SMTLIBv2Parser.ResponseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#response}.
	 * @param ctx the parse tree
	 */
	void exitResponse(SMTLIBv2Parser.ResponseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#generalReservedWord}.
	 * @param ctx the parse tree
	 */
	void enterGeneralReservedWord(SMTLIBv2Parser.GeneralReservedWordContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#generalReservedWord}.
	 * @param ctx the parse tree
	 */
	void exitGeneralReservedWord(SMTLIBv2Parser.GeneralReservedWordContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void enterSimpleSymbol(SMTLIBv2Parser.SimpleSymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 */
	void exitSimpleSymbol(SMTLIBv2Parser.SimpleSymbolContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#quotedSymbol}.
	 * @param ctx the parse tree
	 */
	void enterQuotedSymbol(SMTLIBv2Parser.QuotedSymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#quotedSymbol}.
	 * @param ctx the parse tree
	 */
	void exitQuotedSymbol(SMTLIBv2Parser.QuotedSymbolContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#predefSymbol}.
	 * @param ctx the parse tree
	 */
	void enterPredefSymbol(SMTLIBv2Parser.PredefSymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#predefSymbol}.
	 * @param ctx the parse tree
	 */
	void exitPredefSymbol(SMTLIBv2Parser.PredefSymbolContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#predefKeyword}.
	 * @param ctx the parse tree
	 */
	void enterPredefKeyword(SMTLIBv2Parser.PredefKeywordContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#predefKeyword}.
	 * @param ctx the parse tree
	 */
	void exitPredefKeyword(SMTLIBv2Parser.PredefKeywordContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void enterSymbol(SMTLIBv2Parser.SymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#symbol}.
	 * @param ctx the parse tree
	 */
	void exitSymbol(SMTLIBv2Parser.SymbolContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#numeral}.
	 * @param ctx the parse tree
	 */
	void enterNumeral(SMTLIBv2Parser.NumeralContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#numeral}.
	 * @param ctx the parse tree
	 */
	void exitNumeral(SMTLIBv2Parser.NumeralContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#decimal}.
	 * @param ctx the parse tree
	 */
	void enterDecimal(SMTLIBv2Parser.DecimalContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#decimal}.
	 * @param ctx the parse tree
	 */
	void exitDecimal(SMTLIBv2Parser.DecimalContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#hexadecimal}.
	 * @param ctx the parse tree
	 */
	void enterHexadecimal(SMTLIBv2Parser.HexadecimalContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#hexadecimal}.
	 * @param ctx the parse tree
	 */
	void exitHexadecimal(SMTLIBv2Parser.HexadecimalContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#binary}.
	 * @param ctx the parse tree
	 */
	void enterBinary(SMTLIBv2Parser.BinaryContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#binary}.
	 * @param ctx the parse tree
	 */
	void exitBinary(SMTLIBv2Parser.BinaryContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#string}.
	 * @param ctx the parse tree
	 */
	void enterString(SMTLIBv2Parser.StringContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#string}.
	 * @param ctx the parse tree
	 */
	void exitString(SMTLIBv2Parser.StringContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void enterKeyword(SMTLIBv2Parser.KeywordContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#keyword}.
	 * @param ctx the parse tree
	 */
	void exitKeyword(SMTLIBv2Parser.KeywordContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterSpec_constant(SMTLIBv2Parser.Spec_constantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitSpec_constant(SMTLIBv2Parser.Spec_constantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterS_expr(SMTLIBv2Parser.S_exprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitS_expr(SMTLIBv2Parser.S_exprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void enterIndex(SMTLIBv2Parser.IndexContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#index}.
	 * @param ctx the parse tree
	 */
	void exitIndex(SMTLIBv2Parser.IndexContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void enterIdentifier(SMTLIBv2Parser.IdentifierContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#identifier}.
	 * @param ctx the parse tree
	 */
	void exitIdentifier(SMTLIBv2Parser.IdentifierContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void enterAttribute_value(SMTLIBv2Parser.Attribute_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 */
	void exitAttribute_value(SMTLIBv2Parser.Attribute_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void enterAttribute(SMTLIBv2Parser.AttributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#attribute}.
	 * @param ctx the parse tree
	 */
	void exitAttribute(SMTLIBv2Parser.AttributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void enterSort(SMTLIBv2Parser.SortContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#sort}.
	 * @param ctx the parse tree
	 */
	void exitSort(SMTLIBv2Parser.SortContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#qual_identifier}.
	 * @param ctx the parse tree
	 */
	void enterQual_identifier(SMTLIBv2Parser.Qual_identifierContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#qual_identifier}.
	 * @param ctx the parse tree
	 */
	void exitQual_identifier(SMTLIBv2Parser.Qual_identifierContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#var_binding}.
	 * @param ctx the parse tree
	 */
	void enterVar_binding(SMTLIBv2Parser.Var_bindingContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#var_binding}.
	 * @param ctx the parse tree
	 */
	void exitVar_binding(SMTLIBv2Parser.Var_bindingContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#sorted_var}.
	 * @param ctx the parse tree
	 */
	void enterSorted_var(SMTLIBv2Parser.Sorted_varContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#sorted_var}.
	 * @param ctx the parse tree
	 */
	void exitSorted_var(SMTLIBv2Parser.Sorted_varContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void enterPattern(SMTLIBv2Parser.PatternContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#pattern}.
	 * @param ctx the parse tree
	 */
	void exitPattern(SMTLIBv2Parser.PatternContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#match_case}.
	 * @param ctx the parse tree
	 */
	void enterMatch_case(SMTLIBv2Parser.Match_caseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#match_case}.
	 * @param ctx the parse tree
	 */
	void exitMatch_case(SMTLIBv2Parser.Match_caseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm(SMTLIBv2Parser.TermContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm(SMTLIBv2Parser.TermContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#sort_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterSort_symbol_decl(SMTLIBv2Parser.Sort_symbol_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#sort_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitSort_symbol_decl(SMTLIBv2Parser.Sort_symbol_declContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#meta_spec_constant}.
	 * @param ctx the parse tree
	 */
	void enterMeta_spec_constant(SMTLIBv2Parser.Meta_spec_constantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#meta_spec_constant}.
	 * @param ctx the parse tree
	 */
	void exitMeta_spec_constant(SMTLIBv2Parser.Meta_spec_constantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterFun_symbol_decl(SMTLIBv2Parser.Fun_symbol_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitFun_symbol_decl(SMTLIBv2Parser.Fun_symbol_declContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void enterPar_fun_symbol_decl(SMTLIBv2Parser.Par_fun_symbol_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 */
	void exitPar_fun_symbol_decl(SMTLIBv2Parser.Par_fun_symbol_declContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void enterTheory_attribute(SMTLIBv2Parser.Theory_attributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 */
	void exitTheory_attribute(SMTLIBv2Parser.Theory_attributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#theory_decl}.
	 * @param ctx the parse tree
	 */
	void enterTheory_decl(SMTLIBv2Parser.Theory_declContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#theory_decl}.
	 * @param ctx the parse tree
	 */
	void exitTheory_decl(SMTLIBv2Parser.Theory_declContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void enterLogic_attribue(SMTLIBv2Parser.Logic_attribueContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 */
	void exitLogic_attribue(SMTLIBv2Parser.Logic_attribueContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#logic}.
	 * @param ctx the parse tree
	 */
	void enterLogic(SMTLIBv2Parser.LogicContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#logic}.
	 * @param ctx the parse tree
	 */
	void exitLogic(SMTLIBv2Parser.LogicContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#sort_dec}.
	 * @param ctx the parse tree
	 */
	void enterSort_dec(SMTLIBv2Parser.Sort_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#sort_dec}.
	 * @param ctx the parse tree
	 */
	void exitSort_dec(SMTLIBv2Parser.Sort_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#selector_dec}.
	 * @param ctx the parse tree
	 */
	void enterSelector_dec(SMTLIBv2Parser.Selector_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#selector_dec}.
	 * @param ctx the parse tree
	 */
	void exitSelector_dec(SMTLIBv2Parser.Selector_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#constructor_dec}.
	 * @param ctx the parse tree
	 */
	void enterConstructor_dec(SMTLIBv2Parser.Constructor_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#constructor_dec}.
	 * @param ctx the parse tree
	 */
	void exitConstructor_dec(SMTLIBv2Parser.Constructor_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void enterDatatype_dec(SMTLIBv2Parser.Datatype_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 */
	void exitDatatype_dec(SMTLIBv2Parser.Datatype_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#function_dec}.
	 * @param ctx the parse tree
	 */
	void enterFunction_dec(SMTLIBv2Parser.Function_decContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#function_dec}.
	 * @param ctx the parse tree
	 */
	void exitFunction_dec(SMTLIBv2Parser.Function_decContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#function_def}.
	 * @param ctx the parse tree
	 */
	void enterFunction_def(SMTLIBv2Parser.Function_defContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#function_def}.
	 * @param ctx the parse tree
	 */
	void exitFunction_def(SMTLIBv2Parser.Function_defContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void enterProp_literal(SMTLIBv2Parser.Prop_literalContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 */
	void exitProp_literal(SMTLIBv2Parser.Prop_literalContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#script}.
	 * @param ctx the parse tree
	 */
	void enterScript(SMTLIBv2Parser.ScriptContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#script}.
	 * @param ctx the parse tree
	 */
	void exitScript(SMTLIBv2Parser.ScriptContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_assert}.
	 * @param ctx the parse tree
	 */
	void enterCmd_assert(SMTLIBv2Parser.Cmd_assertContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_assert}.
	 * @param ctx the parse tree
	 */
	void exitCmd_assert(SMTLIBv2Parser.Cmd_assertContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_checkSat}.
	 * @param ctx the parse tree
	 */
	void enterCmd_checkSat(SMTLIBv2Parser.Cmd_checkSatContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_checkSat}.
	 * @param ctx the parse tree
	 */
	void exitCmd_checkSat(SMTLIBv2Parser.Cmd_checkSatContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_checkSatAssuming}.
	 * @param ctx the parse tree
	 */
	void enterCmd_checkSatAssuming(SMTLIBv2Parser.Cmd_checkSatAssumingContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_checkSatAssuming}.
	 * @param ctx the parse tree
	 */
	void exitCmd_checkSatAssuming(SMTLIBv2Parser.Cmd_checkSatAssumingContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_declareConst}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareConst(SMTLIBv2Parser.Cmd_declareConstContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareConst}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareConst(SMTLIBv2Parser.Cmd_declareConstContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_declareDatatype}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareDatatype(SMTLIBv2Parser.Cmd_declareDatatypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareDatatype}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareDatatype(SMTLIBv2Parser.Cmd_declareDatatypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_declareDatatypes}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareDatatypes(SMTLIBv2Parser.Cmd_declareDatatypesContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareDatatypes}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareDatatypes(SMTLIBv2Parser.Cmd_declareDatatypesContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_declareFun}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareFun(SMTLIBv2Parser.Cmd_declareFunContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareFun}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareFun(SMTLIBv2Parser.Cmd_declareFunContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_declareSort}.
	 * @param ctx the parse tree
	 */
	void enterCmd_declareSort(SMTLIBv2Parser.Cmd_declareSortContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareSort}.
	 * @param ctx the parse tree
	 */
	void exitCmd_declareSort(SMTLIBv2Parser.Cmd_declareSortContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFun}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineFun(SMTLIBv2Parser.Cmd_defineFunContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFun}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineFun(SMTLIBv2Parser.Cmd_defineFunContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFunRec}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineFunRec(SMTLIBv2Parser.Cmd_defineFunRecContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFunRec}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineFunRec(SMTLIBv2Parser.Cmd_defineFunRecContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFunsRec}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineFunsRec(SMTLIBv2Parser.Cmd_defineFunsRecContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFunsRec}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineFunsRec(SMTLIBv2Parser.Cmd_defineFunsRecContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_defineSort}.
	 * @param ctx the parse tree
	 */
	void enterCmd_defineSort(SMTLIBv2Parser.Cmd_defineSortContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineSort}.
	 * @param ctx the parse tree
	 */
	void exitCmd_defineSort(SMTLIBv2Parser.Cmd_defineSortContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_echo}.
	 * @param ctx the parse tree
	 */
	void enterCmd_echo(SMTLIBv2Parser.Cmd_echoContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_echo}.
	 * @param ctx the parse tree
	 */
	void exitCmd_echo(SMTLIBv2Parser.Cmd_echoContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_exit}.
	 * @param ctx the parse tree
	 */
	void enterCmd_exit(SMTLIBv2Parser.Cmd_exitContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_exit}.
	 * @param ctx the parse tree
	 */
	void exitCmd_exit(SMTLIBv2Parser.Cmd_exitContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getAssertions}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getAssertions(SMTLIBv2Parser.Cmd_getAssertionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getAssertions}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getAssertions(SMTLIBv2Parser.Cmd_getAssertionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getAssignment}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getAssignment(SMTLIBv2Parser.Cmd_getAssignmentContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getAssignment}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getAssignment(SMTLIBv2Parser.Cmd_getAssignmentContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getInfo}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getInfo(SMTLIBv2Parser.Cmd_getInfoContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getInfo}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getInfo(SMTLIBv2Parser.Cmd_getInfoContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getModel}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getModel(SMTLIBv2Parser.Cmd_getModelContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getModel}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getModel(SMTLIBv2Parser.Cmd_getModelContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getOption}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getOption(SMTLIBv2Parser.Cmd_getOptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getOption}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getOption(SMTLIBv2Parser.Cmd_getOptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getProof}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getProof(SMTLIBv2Parser.Cmd_getProofContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getProof}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getProof(SMTLIBv2Parser.Cmd_getProofContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getUnsatAssumptions}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getUnsatAssumptions(SMTLIBv2Parser.Cmd_getUnsatAssumptionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getUnsatAssumptions}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getUnsatAssumptions(SMTLIBv2Parser.Cmd_getUnsatAssumptionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getUnsatCore}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getUnsatCore(SMTLIBv2Parser.Cmd_getUnsatCoreContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getUnsatCore}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getUnsatCore(SMTLIBv2Parser.Cmd_getUnsatCoreContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_getValue}.
	 * @param ctx the parse tree
	 */
	void enterCmd_getValue(SMTLIBv2Parser.Cmd_getValueContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_getValue}.
	 * @param ctx the parse tree
	 */
	void exitCmd_getValue(SMTLIBv2Parser.Cmd_getValueContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_pop}.
	 * @param ctx the parse tree
	 */
	void enterCmd_pop(SMTLIBv2Parser.Cmd_popContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_pop}.
	 * @param ctx the parse tree
	 */
	void exitCmd_pop(SMTLIBv2Parser.Cmd_popContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_push}.
	 * @param ctx the parse tree
	 */
	void enterCmd_push(SMTLIBv2Parser.Cmd_pushContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_push}.
	 * @param ctx the parse tree
	 */
	void exitCmd_push(SMTLIBv2Parser.Cmd_pushContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_reset}.
	 * @param ctx the parse tree
	 */
	void enterCmd_reset(SMTLIBv2Parser.Cmd_resetContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_reset}.
	 * @param ctx the parse tree
	 */
	void exitCmd_reset(SMTLIBv2Parser.Cmd_resetContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_resetAssertions}.
	 * @param ctx the parse tree
	 */
	void enterCmd_resetAssertions(SMTLIBv2Parser.Cmd_resetAssertionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_resetAssertions}.
	 * @param ctx the parse tree
	 */
	void exitCmd_resetAssertions(SMTLIBv2Parser.Cmd_resetAssertionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_setInfo}.
	 * @param ctx the parse tree
	 */
	void enterCmd_setInfo(SMTLIBv2Parser.Cmd_setInfoContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_setInfo}.
	 * @param ctx the parse tree
	 */
	void exitCmd_setInfo(SMTLIBv2Parser.Cmd_setInfoContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_setLogic}.
	 * @param ctx the parse tree
	 */
	void enterCmd_setLogic(SMTLIBv2Parser.Cmd_setLogicContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_setLogic}.
	 * @param ctx the parse tree
	 */
	void exitCmd_setLogic(SMTLIBv2Parser.Cmd_setLogicContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#cmd_setOption}.
	 * @param ctx the parse tree
	 */
	void enterCmd_setOption(SMTLIBv2Parser.Cmd_setOptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#cmd_setOption}.
	 * @param ctx the parse tree
	 */
	void exitCmd_setOption(SMTLIBv2Parser.Cmd_setOptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void enterCommand(SMTLIBv2Parser.CommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#command}.
	 * @param ctx the parse tree
	 */
	void exitCommand(SMTLIBv2Parser.CommandContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#b_value}.
	 * @param ctx the parse tree
	 */
	void enterB_value(SMTLIBv2Parser.B_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#b_value}.
	 * @param ctx the parse tree
	 */
	void exitB_value(SMTLIBv2Parser.B_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void enterOption(SMTLIBv2Parser.OptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#option}.
	 * @param ctx the parse tree
	 */
	void exitOption(SMTLIBv2Parser.OptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void enterInfo_flag(SMTLIBv2Parser.Info_flagContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#info_flag}.
	 * @param ctx the parse tree
	 */
	void exitInfo_flag(SMTLIBv2Parser.Info_flagContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#error_behaviour}.
	 * @param ctx the parse tree
	 */
	void enterError_behaviour(SMTLIBv2Parser.Error_behaviourContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#error_behaviour}.
	 * @param ctx the parse tree
	 */
	void exitError_behaviour(SMTLIBv2Parser.Error_behaviourContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void enterReason_unknown(SMTLIBv2Parser.Reason_unknownContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 */
	void exitReason_unknown(SMTLIBv2Parser.Reason_unknownContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void enterModel_response(SMTLIBv2Parser.Model_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#model_response}.
	 * @param ctx the parse tree
	 */
	void exitModel_response(SMTLIBv2Parser.Model_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void enterInfo_response(SMTLIBv2Parser.Info_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#info_response}.
	 * @param ctx the parse tree
	 */
	void exitInfo_response(SMTLIBv2Parser.Info_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#valuation_pair}.
	 * @param ctx the parse tree
	 */
	void enterValuation_pair(SMTLIBv2Parser.Valuation_pairContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#valuation_pair}.
	 * @param ctx the parse tree
	 */
	void exitValuation_pair(SMTLIBv2Parser.Valuation_pairContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#t_valuation_pair}.
	 * @param ctx the parse tree
	 */
	void enterT_valuation_pair(SMTLIBv2Parser.T_valuation_pairContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#t_valuation_pair}.
	 * @param ctx the parse tree
	 */
	void exitT_valuation_pair(SMTLIBv2Parser.T_valuation_pairContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#check_sat_response}.
	 * @param ctx the parse tree
	 */
	void enterCheck_sat_response(SMTLIBv2Parser.Check_sat_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#check_sat_response}.
	 * @param ctx the parse tree
	 */
	void exitCheck_sat_response(SMTLIBv2Parser.Check_sat_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#echo_response}.
	 * @param ctx the parse tree
	 */
	void enterEcho_response(SMTLIBv2Parser.Echo_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#echo_response}.
	 * @param ctx the parse tree
	 */
	void exitEcho_response(SMTLIBv2Parser.Echo_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_assertions_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_assertions_response(SMTLIBv2Parser.Get_assertions_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_assertions_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_assertions_response(SMTLIBv2Parser.Get_assertions_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_assignment_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_assignment_response(SMTLIBv2Parser.Get_assignment_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_assignment_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_assignment_response(SMTLIBv2Parser.Get_assignment_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_info_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_info_response(SMTLIBv2Parser.Get_info_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_info_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_info_response(SMTLIBv2Parser.Get_info_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_model_response(SMTLIBv2Parser.Get_model_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_model_response(SMTLIBv2Parser.Get_model_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_option_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_option_response(SMTLIBv2Parser.Get_option_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_option_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_option_response(SMTLIBv2Parser.Get_option_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_proof_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_proof_response(SMTLIBv2Parser.Get_proof_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_proof_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_proof_response(SMTLIBv2Parser.Get_proof_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_unsat_assump_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_unsat_assump_response(SMTLIBv2Parser.Get_unsat_assump_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_unsat_assump_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_unsat_assump_response(SMTLIBv2Parser.Get_unsat_assump_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_unsat_core_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_unsat_core_response(SMTLIBv2Parser.Get_unsat_core_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_unsat_core_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_unsat_core_response(SMTLIBv2Parser.Get_unsat_core_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#get_value_response}.
	 * @param ctx the parse tree
	 */
	void enterGet_value_response(SMTLIBv2Parser.Get_value_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#get_value_response}.
	 * @param ctx the parse tree
	 */
	void exitGet_value_response(SMTLIBv2Parser.Get_value_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void enterSpecific_success_response(SMTLIBv2Parser.Specific_success_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 */
	void exitSpecific_success_response(SMTLIBv2Parser.Specific_success_responseContext ctx);
	/**
	 * Enter a parse tree produced by {@link SMTLIBv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void enterGeneral_response(SMTLIBv2Parser.General_responseContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTLIBv2Parser#general_response}.
	 * @param ctx the parse tree
	 */
	void exitGeneral_response(SMTLIBv2Parser.General_responseContext ctx);
}