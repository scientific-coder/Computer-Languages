// (C) Bernard Hugueney, licence GPL v3
#include <string>
#include <iostream>

#include <boost/utility/enable_if.hpp>
#include <boost/type_traits/is_same.hpp>
#include <boost/type_traits/is_integral.hpp>
#include <boost/type_traits/is_floating_point.hpp>
#include <boost/mpl/if.hpp>
#include <boost/mpl/or.hpp>
#include <boost/mpl/and.hpp>

#include <boost/mpl/placeholders.hpp>
#include <boost/mpl/bool.hpp>
#include <boost/mpl/fold.hpp>
#include <boost/mpl/or.hpp>
#include <boost/mpl/and.hpp>
#include <boost/mpl/vector.hpp>
#include <boost/mpl/map.hpp>

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_function.hpp>
#include <boost/spirit/home/phoenix/fusion/at.hpp>
#include <boost/spirit/home/qi/string/symbols.hpp>

#include <llvm/LLVMContext.h>
#include <llvm/Module.h>
#include <llvm/Function.h>
#include <llvm/PassManager.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Assembly/PrintModulePass.h>
#include <llvm/Support/IRBuilder.h>
//#include "IRBuilderNoFold.h" // local hack to remove constant folding for illustrative purposes
#include <llvm/Support/raw_ostream.h>



using namespace llvm;
/*

lang_3 : variables declarations and assignments with infix arithmetic expressions,
if {}[else{}] and ternary operator.
 ends with a return statement.

Still missing variable scopes.

Default llvm Internal Representation Builder does constant folding.

Variables mapping name->adress is handled directly by spirit::symbols<>

Much of the code is there only to enable support for all signed numeric types (short, int, long, float, double) as valid value_t.

*/

// time g++ -o lang_3-llvm lang_3-llvm.cxx `llvm-config-2.8 --cppflags --ldflags --libs core` -lstdc++

using namespace boost::spirit;
using namespace boost::spirit::qi;
using namespace boost::spirit::ascii;


// template function to map  C++ type -> llvm::Type
template<typename T> static const Type* type(){ return "unkown type!";}// error
template<> const Type* type<void>()  { return Type::getVoidTy(getGlobalContext());}
template<> const Type* type<int>()   { return Type::getInt32Ty(getGlobalContext());}
template<> const Type* type<long>()  { return Type::getInt64Ty(getGlobalContext());}
template<> const Type* type<float>() { return Type::getFloatTy(getGlobalContext());}
template<> const Type* type<double>(){ return Type::getDoubleTy(getGlobalContext());}

// template structs to map C++ type -> Spirit2 numeric parser
template<typename T> struct numeric_parser{};

template<>  struct numeric_parser<short>{
  typedef const short__type type;
  static type parser;
};
numeric_parser<short>::type numeric_parser<short>::parser=short_;

template<> struct   numeric_parser<int>{
  typedef const int__type type;
  static type parser;
};
numeric_parser<int>::type numeric_parser<int>::parser=int_;

template<>  struct  numeric_parser<long>{
  typedef const long__type type;
  static type parser;
};
numeric_parser<long>::type numeric_parser<long>::parser=long_;

template<>  struct  numeric_parser<float>{
  typedef const float__type type;
  static type parser;
};
numeric_parser<float>::type numeric_parser<float>::parser=float_;

template<>  struct  numeric_parser<double>{
  typedef const double__type type;
  static type parser;
};

numeric_parser<double>::type numeric_parser<double>::parser=double_;

template<>  struct  numeric_parser<long double>{
  typedef const long_double_type type;
  static type parser;
};

numeric_parser<long double>::type numeric_parser<long double>::parser=long_double;

// now the real deal, at last ! :-)
// arithmetic expression grammar, using semantic actions to create llvm internal representation
template <typename value_t, typename Iterator>
struct language_3_grammar : grammar<Iterator, boost::spirit::standard::space_type> {

  // symbols map use to store varables names and map them to the relevant llvm node
  typedef boost::spirit::qi::symbols<char,AllocaInst*> vars_t;

  //only used to select overload of builder_helper operator()
  struct return_tag{}; struct if_tag{}; struct else_tag{}; struct end_if_tag{};
  struct end_ternary_tag{};

  // data created when generating the "if", to be used by "else" and "end_if" generations
  typedef boost::fusion::vector<Function*, BasicBlock*, BasicBlock*, BasicBlock*> if_then_else_t;


  template<Value* (IRBuilder<>::*)(Value*, Value*, const Twine&)> struct binary_op{};
  template<Value* (IRBuilder<>::*)(Value*, const Twine&)> struct unary_op{};

  typedef binary_op<&IRBuilder<>::CreateAdd> add_t;//
  typedef binary_op<&IRBuilder<>::CreateSub> sub_t;
  typedef binary_op<&IRBuilder<>::CreateMul> mul_t;//
  typedef binary_op<&IRBuilder<>::CreateSDiv> div_t;
  typedef unary_op<&IRBuilder<>::CreateNeg> neg_t; //


  typedef binary_op<&IRBuilder<>::CreateOr> logical_or_t; //
  typedef binary_op<&IRBuilder<>::CreateAnd> logical_and_t;//
  typedef unary_op<&IRBuilder<>::CreateNot> logical_not_t;
  // different methods for integral types and fp types
  typedef typename boost::mpl::if_<boost::is_integral<value_t>
	       , binary_op<&IRBuilder<>::CreateICmpSGT>
	       , binary_op<&IRBuilder<>::CreateFCmpOGT> >::type greater_than_t;
  typedef typename boost::mpl::if_<boost::is_integral<value_t>
				   , binary_op<&IRBuilder<>::CreateICmpSLT>//
		     , binary_op<&IRBuilder<>::CreateFCmpOLT> >::type lesser_than_t;
  typedef typename boost::mpl::if_<boost::is_integral<value_t>
		       ,binary_op<&IRBuilder<>::CreateICmpSGE>
		       ,binary_op<&IRBuilder<>::CreateFCmpOGE> >::type greater_or_eq_t;
typedef typename boost::mpl::if_<boost::is_integral<value_t>
		     ,binary_op<&IRBuilder<>::CreateICmpSLE>
		     ,binary_op<&IRBuilder<>::CreateFCmpOLE> >::type lesser_or_eq_t;
typedef typename boost::mpl::if_<boost::is_integral<value_t>
		     ,binary_op<&IRBuilder<>::CreateICmpEQ>
		     ,binary_op<&IRBuilder<>::CreateFCmpOEQ> >::type equality_t;
typedef typename boost::mpl::if_<boost::is_integral<value_t>
		     ,binary_op<&IRBuilder<>::CreateICmpNE>
		     ,binary_op<&IRBuilder<>::CreateFCmpONE> >::type inequality_t;


// functor structure used to create llvm internal representation
// (ab)using a lot boost::phoenix::function<> ability to overload operator() !
struct builder_helper{

  // template structs to have different result type according to the argument types
  template<typename T1, typename T2=void, typename T3=void, typename T4=void> 
  struct result {
    // dispatch on first arg type using a map to handle most cases
  typedef typename boost::mpl::at<boost::mpl::map<boost::mpl::pair<AllocaInst*, Value*>
						    , boost::mpl::pair<std::string, AllocaInst*>
						    , boost::mpl::pair<return_tag, ReturnInst*>
						    , boost::mpl::pair<if_tag, if_then_else_t>
						    , boost::mpl::pair<else_tag, void>
						    , boost::mpl::pair<end_if_tag, void> >
				    , T1 >::type need_default;
    // (AllocaInst*, Value*) is a store, not a read, so we set return type to StoreInst* instead of Value*
    // and set default to Value* instead of void_
  typedef typename boost::mpl::if_<
    boost::is_same< 
      typename boost::mpl::if_<boost::mpl::and_<boost::is_same<T1, AllocaInst*>
						,boost::is_same<T2, Value*> >
			       , StoreInst* , need_default>::type, boost::mpl::void_>
				 , Value*
    , need_default>::type type;
};

  builder_helper(vars_t &v, IRBuilder<>& b):vars(v), builder(b){}
  
  // floating point logical operations return integral (because boolean) results
  // hence we must cast them back to fp when needed (cast_result(Value*)).
  // Metaprogramming utilities to select at compile time wether casting to fp is needed
  // (logical op & fp value_t), otherwise (arithmetic op | integral ) cast_result() does nothing.
  typedef boost::fusion::vector<add_t, sub_t, mul_t, div_t, neg_t> arithmetic_ops;
  typedef boost::fusion::vector<equality_t, inequality_t
				, logical_or_t, logical_and_t, logical_not_t
				, greater_than_t, lesser_than_t, lesser_or_eq_t, greater_or_eq_t>
  logical_ops;

  template<typename T, typename V> struct is_in // is type V in types sequence V ?
  : boost::mpl::fold<V, boost::mpl::false_, boost::mpl::or_<boost::mpl::_1, boost::is_same<T, boost::mpl::_2> > > {};
  template<typename T> 
  typename boost::enable_if<boost::mpl::or_<is_in<T,arithmetic_ops>
				, boost::is_integral<value_t> >, Value* 
			    >::type cast_result(Value* v) const { return v; }

  template<typename T> 
  typename boost::enable_if<boost::mpl::and_<is_in<T, logical_ops>
				 , boost::is_floating_point<value_t> >, Value*
			    >::type cast_result(Value* v) const
  { return builder.CreateUIToFP(v, type<value_t>(), "bool_to_fp_tmp"); }
    
  // binary operations
  template< Value*(IRBuilder<>::* const mem_fun)(Value*, Value*, const Twine&)>
  Value* operator()(binary_op<mem_fun> /* unused */, Value* a1, Value* a2, const char * name) const
  { return cast_result<binary_op<mem_fun> >((builder.*mem_fun)(a1, a2, name)); }

  // unary operation
  template< Value*(IRBuilder<>::* const mem_fun)(Value*, const Twine&)>
  Value* operator()(unary_op<mem_fun>/* unused */, Value* a, const char * name) const
  { return cast_result<unary_op<mem_fun> >((builder.*mem_fun)(a, name)); }

  // return instruction
  ReturnInst* operator()(return_tag /* unused */, Value*  a) const { return builder.CreateRet(a); }

  // variable assignment
  StoreInst* operator()(AllocaInst* variable, Value* value ) const
  { return builder.CreateStore(value, variable, false); }

  // reading a variable value
  Value* operator()(AllocaInst* variable) const {return builder.CreateLoad(variable);}

  // variable declaration
  AllocaInst* operator()(std::string const& name) const{
    AllocaInst* res(builder.CreateAlloca(type<value_t>(),0, name.c_str()));
    vars.add(name.begin(), name.end(), res);
    return res;
  }
  // if statement : performs test and create then, else and end_if BasicBlock
  // returns <parent_function, else_BB, end_if_BB> to be used by else and end_if statements
  if_then_else_t operator()(if_tag /*unused*/, Value *expression) const{
    // get pointer to parent_function and create instruction blocks
    Function * parent_function = builder.GetInsertBlock()->getParent();
    BasicBlock * then_BB = BasicBlock::Create(getGlobalContext(), " then", parent_function);
    BasicBlock * else_BB = BasicBlock::Create(getGlobalContext()," else");
    BasicBlock * end_if_BB = BasicBlock::Create(getGlobalContext()," end_if");
    // create test & branch instruction      
    builder.CreateCondBr(builder.CreateIsNull(expression, "if"), else_BB, then_BB); 
    builder.SetInsertPoint(then_BB); // set then block and start using it
    // return data to be used for else block and end_if
    return if_then_else_t(parent_function, then_BB, else_BB, end_if_BB);
  }

  // else statement : called even when there is no "else{...}" in the code to close then block 
  // and start (possibly empty) else block 
  void operator()(else_tag /* unused */, if_then_else_t const & parent_then_else_endif) const {
    builder.CreateBr(boost::fusion::at_c<3>(parent_then_else_endif));// jump to endif
    boost::fusion::at_c<0>(parent_then_else_endif)
      ->getBasicBlockList().push_back(boost::fusion::at_c<2>(parent_then_else_endif));
    builder.SetInsertPoint(boost::fusion::at_c<2>(parent_then_else_endif));// set else block
    return ;
  }

  void operator()(end_if_tag /*unused */, Function* parent_function, BasicBlock* end_if_BB) const {
    builder.CreateBr(end_if_BB); // jump to end_if
    parent_function->getBasicBlockList().push_back(end_if_BB);// set end_if block
    builder.SetInsertPoint(end_if_BB); // and start using it
    return ;
  }
  Value* operator()(end_ternary_tag /*unused*/, if_then_else_t const& p_t_e_e
		    , Value* then_v, Value* else_v) const {
    (*this)(end_if_tag(), boost::fusion::at_c<0>(p_t_e_e), boost::fusion::at_c<3>(p_t_e_e));
    PHINode * phi = builder.CreatePHI(type<value_t>(),"ternary_merge");
    phi->addIncoming(then_v, boost::fusion::at_c<1>(p_t_e_e));
    phi->addIncoming(else_v, boost::fusion::at_c<2>(p_t_e_e));
    return phi;
  }


  // constant values
  Value* operator()(short v) const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(short)*8, v)); }
  Value* operator()(int v)   const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(int)*8, v)); }
  Value* operator()(long v)  const { return ConstantInt::get(getGlobalContext(), APInt(sizeof(long)*8, v)); }
  Value* operator()(float v) const { return ConstantFP::get(getGlobalContext(), APFloat(v)); }// APFloat()
  Value* operator()(double v)const { return ConstantFP::get(getGlobalContext(), APFloat(v)); }// is overloaded

  vars_t& vars;
  IRBuilder<>& builder;
};

language_3_grammar( IRBuilder<>& p) 
  : language_3_grammar::base_type(program), build(builder_helper(vars, p)){
  reserved_keywords = "var", "return", "if", "else";

  program =  code_block >> return_statement;

  code_block = *(variable_declaration | assignment | if_then_else);
  // we want to enforce the space after "return" so we must disable the skipper with lexeme[]
  return_statement = lexeme["return" >> boost::spirit::standard::space] >> additive_expression[_val=build(return_tag(), _1)]>>';' ;

  if_then_else = lit("if") 
    // build(if_tag, test_expression) returns <parent_function, else_block, end_if_block>
    >> '(' >> expression[_a=build(if_tag(),_1)] >> ')'
    //build(else_tag, parent_function, if_then_else_return_t) must be called even when there
    // is no else clause to create an empty one as target when test expression is false
    >> '{' >> code_block >> boost::spirit::standard::char_('}')[build(else_tag(), _a)]
    >> -( lit("else") >> '{' >> code_block >> '}' )
    // build(end_if_tag(), parent_function, end_if_block) must always be called 
    >> eps[build(end_if_tag(), boost::phoenix::at_c<0>(_a), boost::phoenix::at_c<3>(_a))]
    ;
  
  expression = ternary_expression[_val= _1];

  ternary_expression =  logical_or_expression[_val=_1]
    >>*( boost::spirit::standard::char_('?')[_a=build(if_tag(),_val)] >> logical_or_expression[_b=_1]
	 >> boost::spirit::standard::char_(':')[build(else_tag(), _a)] 
	 >> logical_or_expression[_val=build(end_ternary_tag(), _a, _b, _1)] ) ;

  logical_or_expression = logical_and_expression[_val=_1]
    >>*("||">>logical_and_expression[_val=build(logical_or_t(), _val, _1, "or_tmp")]);

  logical_and_expression = equality_expression[_val = _1]
    >>*("&&">>equality_expression[_val=build(logical_and_t(), _val, _1,"and_tmp")]);

  equality_expression = compare_expression[_val=_1]
    >>*("==">>logical_and_expression[_val=build(equality_t(), _val, _1,"eq_tmp")]
	|"!=">>logical_and_expression[_val=build(inequality_t(), _val, _1,"ineq_tmp")]
	);

  compare_expression = additive_expression[_val=_1]
    >>*('<'>>additive_expression[_val=build(lesser_than_t(), _val, _1,"lt_tmp")]
	|'>'>>additive_expression[_val=build(greater_than_t(), _val, _1,"gt_tmp")]
	|"<=">>additive_expression[_val=build(lesser_or_eq_t(), _val, _1, "le_tmp")]
	|">=">>additive_expression[_val=build(greater_or_eq_t(), _val, _1, "ge_tmp")]
	);

  additive_expression =
    multiplicative_expression               [_val=_1]
    >> *(
	 ('+' >> multiplicative_expression 
	  [_val= build(add_t(), _val, _1,"addtmp")])
	 |('-' >> multiplicative_expression 
	   [_val=build(sub_t(), _val, _1,"subtmp")])
	 )
    ;
  multiplicative_expression =
    unary_expression               [_val=_1]
    >> *(
	 ('*' >> unary_expression[_val= build(mul_t(), _val, _1, "multmp")])
	 |('/' >> unary_expression [_val = build(div_t(), _val, _1, "divtmp")])
	 )
    ;
  unary_expression =
    primary_expression[_val = _1]
    |   ('-' >> primary_expression[_val= build(neg_t(), _1,"negtmp")])
    |   ('+' >> primary_expression[_val= _1])
    ;
  primary_expression =
    numeric_to_val             [_val=_1]
    | id_declared_var [_val=build(_1)]
    | '(' >> ternary_expression  [_val=_1] >> ')'
    ;
  numeric_to_val = numeric_parser<value_t>::parser[_val=build(_1)];

  variable = id_declared_var[_val=build(_1)];

  id_declaration %= raw[lexeme[boost::spirit::standard::alpha >> *(boost::spirit::standard::alnum | '_')]] ;//lexeme disables skipping for >>

  id_declared_var = lexeme[ vars [_val = _1] // ditto for lexeme, id must be in vars
			    >> !(boost::spirit::standard::alnum | '_')]; // prevents partial match with only a prefix
  
  variable_declaration = "var" >> !id_declared_var // disallow redeclaration of variables
			       >> !reserved_keywords
			       >> id_declaration [_a = build(_1)]
			       >> (';' | '=' >> assignment_rhs(_a));
  // id_declared_var returns the AllocaInst* of the variable
  assignment = id_declared_var [_a = _1] >> '=' >> assignment_rhs(_a);
    
  assignment_rhs = expression[_a=_1] >> boost::spirit::standard::char_(';')[build(_r1, _a)];
    
}

boost::spirit::qi::symbols<char, unused_type> reserved_keywords;
vars_t vars;

boost::phoenix::function<builder_helper> build;
  
rule<Iterator, Value*(), boost::spirit::standard::space_type> expression
  , logical_or_expression, logical_and_expression, equality_expression, compare_expression
  , additive_expression,  multiplicative_expression, unary_expression, primary_expression
  , numeric_to_val, variable ;
rule<Iterator, Value*(), locals<if_then_else_t, Value*>, boost::spirit::standard::space_type> ternary_expression;
rule<Iterator, locals<AllocaInst*>, boost::spirit::standard::space_type> variable_declaration, assignment;
rule<Iterator, AllocaInst*(), boost::spirit::standard::space_type> id_declared_var;
rule<Iterator, std::string(), boost::spirit::standard::space_type> id_declaration;
rule<Iterator, boost::spirit::standard::space_type> program, code_block, return_statement;
rule<Iterator, locals<if_then_else_t>, boost::spirit::standard::space_type> if_then_else;
rule<Iterator, void(AllocaInst*), locals<Value*>, boost::spirit::standard::space_type> assignment_rhs;
};

int main(int argc, char* argv[]){
  typedef float value_t; // type used in arithmetic computations

  std::cin.unsetf(std::ios::skipws); //  Turn off white space skipping on the stream
  typedef std::string buffer_t;
  buffer_t buffer(std::istream_iterator<char>(std::cin), (std::istream_iterator<char>()));
  typedef buffer_t::const_iterator iter_t;
  iter_t iter(buffer.begin()), end(buffer.end());

  typedef language_3_grammar<value_t, iter_t> grammar_t;
  Module module("lang_3", getGlobalContext());
  IRBuilder<> p(BasicBlock::Create(getGlobalContext(), "entry",
				   cast<Function>(module.getOrInsertFunction("main"
									     , type<value_t>()
									     , NULL))));
  grammar_t grammar(p);
  bool r = phrase_parse(iter, end, grammar, boost::spirit::standard::space);// allow trailing spaces
  if (r && iter == end) {
    std::cout<<"parsing succeded !\n";
    verifyModule(module, PrintMessageAction);
    PassManager PM;
    std::string out_data;
    llvm::raw_string_ostream output(out_data);
    PM.add(createPrintModulePass(&output));
    PM.run(module);
    std::cout<<output.str();
  } else {
    std::string rest(iter, end);
    std::cerr << "parsing failed\n" << "stopped at: \"" << rest << "\"\n";
  }
  return r ? 0 : 1 ;
}

template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateNeg(llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateOr(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateAnd(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateICmpSLT(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateAdd(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateMul(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateICmpNE(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateICmpSGT(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateSub(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateSDiv(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateICmpSLE(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateICmpSGE(llvm::Value*, llvm::Value*, llvm::Twine const&);

template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateFCmpOEQ(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateFCmpOLT(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateFCmpONE(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateFCmpOGT(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateFCmpOLE(llvm::Value*, llvm::Value*, llvm::Twine const&);
template Value* llvm::IRBuilder<true, llvm::ConstantFolder, llvm::IRBuilderDefaultInserter<true> >::CreateFCmpOGE(llvm::Value*, llvm::Value*, llvm::Twine const&);

