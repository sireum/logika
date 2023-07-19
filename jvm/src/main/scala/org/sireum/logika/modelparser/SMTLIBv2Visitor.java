// Generated from /run/media/mmcblk0p1/Sireum/logika/jvm/src/main/scala/org/sireum/logika/SMTLIBv2.g4 by ANTLR 4.12.0
package org.sireum.logika.modelparser;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link SMTLIBv2Parser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface SMTLIBv2Visitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#start}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStart(SMTLIBv2Parser.StartContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitResponse(SMTLIBv2Parser.ResponseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#generalReservedWord}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneralReservedWord(SMTLIBv2Parser.GeneralReservedWordContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#simpleSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSimpleSymbol(SMTLIBv2Parser.SimpleSymbolContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#quotedSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuotedSymbol(SMTLIBv2Parser.QuotedSymbolContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#predefSymbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPredefSymbol(SMTLIBv2Parser.PredefSymbolContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#predefKeyword}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPredefKeyword(SMTLIBv2Parser.PredefKeywordContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#symbol}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSymbol(SMTLIBv2Parser.SymbolContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#numeral}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNumeral(SMTLIBv2Parser.NumeralContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#decimal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecimal(SMTLIBv2Parser.DecimalContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#hexadecimal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitHexadecimal(SMTLIBv2Parser.HexadecimalContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#binary}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinary(SMTLIBv2Parser.BinaryContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#string}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitString(SMTLIBv2Parser.StringContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#keyword}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitKeyword(SMTLIBv2Parser.KeywordContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec_constant(SMTLIBv2Parser.Spec_constantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitS_expr(SMTLIBv2Parser.S_exprContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#index}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIndex(SMTLIBv2Parser.IndexContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#identifier}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdentifier(SMTLIBv2Parser.IdentifierContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#attribute_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribute_value(SMTLIBv2Parser.Attribute_valueContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribute(SMTLIBv2Parser.AttributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#sort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort(SMTLIBv2Parser.SortContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#qual_identifier}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQual_identifier(SMTLIBv2Parser.Qual_identifierContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#var_binding}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVar_binding(SMTLIBv2Parser.Var_bindingContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#sorted_var}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSorted_var(SMTLIBv2Parser.Sorted_varContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#pattern}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPattern(SMTLIBv2Parser.PatternContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#match_case}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMatch_case(SMTLIBv2Parser.Match_caseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTerm(SMTLIBv2Parser.TermContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#sort_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort_symbol_decl(SMTLIBv2Parser.Sort_symbol_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#meta_spec_constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMeta_spec_constant(SMTLIBv2Parser.Meta_spec_constantContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFun_symbol_decl(SMTLIBv2Parser.Fun_symbol_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#par_fun_symbol_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPar_fun_symbol_decl(SMTLIBv2Parser.Par_fun_symbol_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#theory_attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_attribute(SMTLIBv2Parser.Theory_attributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#theory_decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTheory_decl(SMTLIBv2Parser.Theory_declContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#logic_attribue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic_attribue(SMTLIBv2Parser.Logic_attribueContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#logic}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogic(SMTLIBv2Parser.LogicContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#sort_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSort_dec(SMTLIBv2Parser.Sort_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#selector_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSelector_dec(SMTLIBv2Parser.Selector_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#constructor_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstructor_dec(SMTLIBv2Parser.Constructor_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#datatype_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDatatype_dec(SMTLIBv2Parser.Datatype_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#function_dec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunction_dec(SMTLIBv2Parser.Function_decContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#function_def}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunction_def(SMTLIBv2Parser.Function_defContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#prop_literal}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProp_literal(SMTLIBv2Parser.Prop_literalContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#script}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitScript(SMTLIBv2Parser.ScriptContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_assert}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_assert(SMTLIBv2Parser.Cmd_assertContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_checkSat}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_checkSat(SMTLIBv2Parser.Cmd_checkSatContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_checkSatAssuming}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_checkSatAssuming(SMTLIBv2Parser.Cmd_checkSatAssumingContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareConst}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareConst(SMTLIBv2Parser.Cmd_declareConstContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareDatatype}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareDatatype(SMTLIBv2Parser.Cmd_declareDatatypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareDatatypes}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareDatatypes(SMTLIBv2Parser.Cmd_declareDatatypesContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareFun}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareFun(SMTLIBv2Parser.Cmd_declareFunContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_declareSort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_declareSort(SMTLIBv2Parser.Cmd_declareSortContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFun}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineFun(SMTLIBv2Parser.Cmd_defineFunContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFunRec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineFunRec(SMTLIBv2Parser.Cmd_defineFunRecContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineFunsRec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineFunsRec(SMTLIBv2Parser.Cmd_defineFunsRecContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_defineSort}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_defineSort(SMTLIBv2Parser.Cmd_defineSortContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_echo}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_echo(SMTLIBv2Parser.Cmd_echoContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_exit}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_exit(SMTLIBv2Parser.Cmd_exitContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getAssertions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getAssertions(SMTLIBv2Parser.Cmd_getAssertionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getAssignment}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getAssignment(SMTLIBv2Parser.Cmd_getAssignmentContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getInfo}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getInfo(SMTLIBv2Parser.Cmd_getInfoContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getModel}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getModel(SMTLIBv2Parser.Cmd_getModelContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getOption}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getOption(SMTLIBv2Parser.Cmd_getOptionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getProof}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getProof(SMTLIBv2Parser.Cmd_getProofContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getUnsatAssumptions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getUnsatAssumptions(SMTLIBv2Parser.Cmd_getUnsatAssumptionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getUnsatCore}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getUnsatCore(SMTLIBv2Parser.Cmd_getUnsatCoreContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_getValue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_getValue(SMTLIBv2Parser.Cmd_getValueContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_pop}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_pop(SMTLIBv2Parser.Cmd_popContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_push}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_push(SMTLIBv2Parser.Cmd_pushContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_reset}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_reset(SMTLIBv2Parser.Cmd_resetContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_resetAssertions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_resetAssertions(SMTLIBv2Parser.Cmd_resetAssertionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_setInfo}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_setInfo(SMTLIBv2Parser.Cmd_setInfoContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_setLogic}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_setLogic(SMTLIBv2Parser.Cmd_setLogicContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#cmd_setOption}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCmd_setOption(SMTLIBv2Parser.Cmd_setOptionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#command}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCommand(SMTLIBv2Parser.CommandContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#b_value}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitB_value(SMTLIBv2Parser.B_valueContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#option}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOption(SMTLIBv2Parser.OptionContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#info_flag}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_flag(SMTLIBv2Parser.Info_flagContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#error_behaviour}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitError_behaviour(SMTLIBv2Parser.Error_behaviourContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#reason_unknown}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReason_unknown(SMTLIBv2Parser.Reason_unknownContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitModel_response(SMTLIBv2Parser.Model_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInfo_response(SMTLIBv2Parser.Info_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#valuation_pair}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitValuation_pair(SMTLIBv2Parser.Valuation_pairContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#t_valuation_pair}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitT_valuation_pair(SMTLIBv2Parser.T_valuation_pairContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#check_sat_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCheck_sat_response(SMTLIBv2Parser.Check_sat_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#echo_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEcho_response(SMTLIBv2Parser.Echo_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_assertions_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_assertions_response(SMTLIBv2Parser.Get_assertions_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_assignment_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_assignment_response(SMTLIBv2Parser.Get_assignment_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_info_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_info_response(SMTLIBv2Parser.Get_info_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_model_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_model_response(SMTLIBv2Parser.Get_model_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_option_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_option_response(SMTLIBv2Parser.Get_option_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_proof_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_proof_response(SMTLIBv2Parser.Get_proof_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_unsat_assump_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_unsat_assump_response(SMTLIBv2Parser.Get_unsat_assump_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_unsat_core_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_unsat_core_response(SMTLIBv2Parser.Get_unsat_core_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#get_value_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGet_value_response(SMTLIBv2Parser.Get_value_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#specific_success_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpecific_success_response(SMTLIBv2Parser.Specific_success_responseContext ctx);
	/**
	 * Visit a parse tree produced by {@link SMTLIBv2Parser#general_response}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeneral_response(SMTLIBv2Parser.General_responseContext ctx);
}