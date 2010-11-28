// (C) Bernard Hugueney, licence GPL v3
// code cleanup thanks to Richard Thomson
// remaining ugliness is my fault (or in your eyes ;) )
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
#include <boost/spirit/include/qi_auto.hpp>

#include <llvm/LLVMContext.h>
#include <llvm/Module.h>
#include <llvm/Function.h>
#include <llvm/PassManager.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Assembly/PrintModulePass.h>
#include <llvm/LinkAllPasses.h>
#include <llvm/Support/IRBuilder.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/DerivedTypes.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/Target/TargetData.h>
#include <llvm/Target/TargetSelect.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/ExecutionEngine/JIT.h>
// see http://lists.cs.uiuc.edu/pipermail/llvm-commits/Week-of-Mon-20101115/112020.html
#include <llvm/Support/NoFolder.h>

/*

  lang_3 : variables declarations and assignments with infix arithmetic expressions,
  if {}[else{}] and ternary operator, while(){} control flow.
  ends with a return statement.

  Still missing variables scopes.

  Default llvm Internal Representation Builder does constant folding it can be
  avoided by passing a NoFolder as template arg to the llvm::IRBuilder<> as shown in comment.

  Variables mapping name->adress is handled directly by spirit::symbols<>

  Much of the code is there only to enable support for all signed numeric types (short, int, long, float, double) as valid value_t.

*/

// time g++ -o lang_3-llvm lang_3-llvm.cxx
//      `llvm-config-2.8 --cppflags --ldflags --libs ` -lstdc++ -Wall -O3 -rdynamic

namespace spirit = boost::spirit;
namespace qi = boost::spirit::qi;
namespace ascii = boost::spirit::ascii;
namespace standard = boost::spirit::standard;
namespace fusn = boost::fusion;
namespace mpl = boost::mpl;


// template function to map  C++ type -> llvm::Type
template<typename T> static const llvm::Type* type(){ return "unkown type!";}// error

#define MAP_INT_TYPE(cpp_type_)                                         \
  template <>                                                           \
  const llvm::Type* type<cpp_type_>() {                                 \
    return llvm::Type::getIntNTy(llvm::getGlobalContext()               \
                                 , sizeof(cpp_type_)*8);                \
  }

#define MAP_TYPE(cpp_type_, fn_)                                        \
  template <>                                                           \
  const llvm::Type* type<cpp_type_>() {                                 \
    return llvm::Type::fn_(llvm::getGlobalContext());                   \
  }

MAP_TYPE(void, getVoidTy)
MAP_INT_TYPE(char)
MAP_INT_TYPE(short)
MAP_INT_TYPE(int)
MAP_INT_TYPE(long)
MAP_INT_TYPE(long long)
MAP_TYPE(float, getFloatTy)
MAP_TYPE(double, getDoubleTy)
// long double is more tricky
#undef MAP_INT_TYPE
#undef MAP_TYPE





// now the real deal, at last ! :-)
// arithmetic expression grammar, using semantic actions to create llvm
// internal representation
using llvm::Function;
using llvm::BasicBlock;
using llvm::Value;
using llvm::Twine;
using llvm::AllocaInst;
using llvm::ReturnInst;
using llvm::StoreInst;

template <typename value_t, typename Iterator, typename Builder>
struct language_3_grammar : qi::grammar<Iterator, standard::space_type> {

  // symbols map use to store variables names and map them to
  // the relevant llvm node
  typedef qi::symbols<char, llvm::AllocaInst*> vars_t;

  //only used to select overload of builder_helper operator()
  struct return_tag {}; 
  struct if_tag {}; struct else_tag {}; struct end_if_tag {};
  struct end_ternary_tag {}; 
  struct while_begin_tag {}; struct while_condition_tag {}; struct while_end_tag {};

  // data created when generating start of blocks (e.g. if, while)
  // it stores the blocks info that will be used when
  // closing blocks (e.g. else, closing '}')
  // (also used when generating ternary operations)
  typedef fusn::vector<llvm::Function*
                       , llvm::BasicBlock*, llvm::BasicBlock*, llvm::BasicBlock*> 
  control_flow_t;

  typedef Value* (Builder::*const builder_fun1_t)(Value* , const Twine &);
  typedef Value* (Builder::*const builder_fun2_t)(Value* , Value* , const Twine& );

  template<builder_fun1_t> struct unary_op {};
  template<builder_fun2_t> struct binary_op {};

  typedef binary_op<&Builder::CreateOr> logical_or_t;
  typedef binary_op<&Builder::CreateAnd> logical_and_t;
  typedef unary_op<&Builder::CreateNot> logical_not_t;

  // different methods for integral types and fp types
#define INT_FLOAT_SELECTION(arity_op_, int_method_, float_method_, type_) \
  typedef typename mpl::if_<boost::is_integral<value_t>,                \
                            arity_op_<&Builder::int_method_>,           \
                            arity_op_<&Builder::float_method_> >::type type_

  INT_FLOAT_SELECTION(unary_op, CreateNeg, CreateFNeg, neg_t);
  INT_FLOAT_SELECTION(binary_op, CreateAdd, CreateFAdd, add_t);
  INT_FLOAT_SELECTION(binary_op, CreateSub, CreateFSub, sub_t);
  INT_FLOAT_SELECTION(binary_op, CreateMul, CreateFMul, mul_t);
  INT_FLOAT_SELECTION(binary_op, CreateSDiv, CreateFDiv, div_t);
  INT_FLOAT_SELECTION(binary_op, CreateICmpSGT, CreateFCmpOGT, greater_than_t);
  INT_FLOAT_SELECTION(binary_op, CreateICmpSLT, CreateFCmpOLT, lesser_than_t);
  INT_FLOAT_SELECTION(binary_op, CreateICmpSGE, CreateFCmpOGE, greater_or_eq_t);
  INT_FLOAT_SELECTION(binary_op, CreateICmpSLE, CreateFCmpOLE, lesser_or_eq_t);
  INT_FLOAT_SELECTION(binary_op, CreateICmpEQ, CreateFCmpOEQ, equality_t);
  INT_FLOAT_SELECTION(binary_op, CreateICmpNE, CreateFCmpONE, inequality_t);

#undef INT_FLOAT_SELECTION


  // functor structure used to create llvm internal representation
  // (ab)using a lot boost::phoenix::function<> ability
  // to overload operator() !
  struct builder_helper {
    // template structs to have different result type according to the argument types
    template<typename T1, typename T2 = void
             , typename T3 = void, typename T4 = void> 
    struct result {
      // dispatch on first arg type using a map to handle most cases
      typedef typename mpl::at< mpl::map<   mpl::pair<AllocaInst*, Value*>
                                            , mpl::pair<std::string, AllocaInst*>
                                            , mpl::pair<return_tag, ReturnInst*>
                                            , mpl::pair<if_tag, control_flow_t>
                                            , mpl::pair<else_tag, void>
                                            , mpl::pair<end_if_tag, void> 
                                            , mpl::pair<while_begin_tag, control_flow_t>
                                            , mpl::pair<while_condition_tag, void>
                                            , mpl::pair<while_end_tag, void> >
                                , T1 >::type need_default;
    // correct type as needed for cases not handeled by the map on first arg type
    typedef typename mpl::if_<
      // (AllocaInst*, Value*) is a store, not a read
      //, so we set return type to StoreInst* instead of Value*
      boost::is_same< 
        typename mpl::if_<mpl::and_< boost::is_same<T1, AllocaInst*>
                                     ,boost::is_same<T2, Value*> >
                          , StoreInst* , need_default>::type
        // and set default to Value* instead of void_        
                            , mpl::void_>
      , Value*, need_default>::type type;
  };
    
  builder_helper(vars_t &v, Builder& b) : vars(v), builder(b), ctx(llvm::getGlobalContext())
  {}
 
  // we only handle one type (value_t) in expressions, but
  // floating point logical operations return integral (because boolean)
  //results hence we must cast them back to fp when needed (cast_result(Value*)).
  // Metaprogramming utilities to select at compile time wether
  // casting to fp is needed (logical op & fp value_t)
  //, otherwise (arithmetic op | integral ) cast_result() does nothing.
  typedef fusn::vector<add_t, sub_t, mul_t, div_t, neg_t> 
  arithmetic_ops;
  typedef fusn::vector<equality_t, inequality_t
                       , logical_or_t, logical_and_t, logical_not_t
                       , greater_than_t, lesser_than_t, lesser_or_eq_t, greater_or_eq_t>
  logical_ops;

  template<typename T, typename V> 
  struct is_in // is type T in types sequence V ?
    : mpl::fold<V, mpl::false_
                , mpl::or_<mpl::_1
                           , boost::is_same<T, mpl::_2> > > 
  {};

  template<typename T> 
  typename boost::enable_if< mpl::or_<is_in<T,arithmetic_ops>
                                      , boost::is_integral<value_t> >
                             , Value*
                             >::type cast_result(Value* v) const { return v; }

    template<typename T> 
    typename boost::enable_if< mpl::and_< is_in<T, logical_ops>
                                          , boost::is_floating_point<value_t> >
                               , Value*
                               >::type cast_result(Value* v) const
                               { return builder.CreateUIToFP(v, type<value_t>(), "bool_to_fp_tmp"); }

// converse is needed for test expecting a boolean
// this is inefficient, conversion to fp should be on demand 
//so that we don't have to convert back to integral.
template<typename T> 
typename boost::enable_if< boost::is_integral<value_t>, T* 
                           >::type to_boolean(T* v) const { return v; }

    template<typename T> 
    typename boost::enable_if<boost::is_floating_point<value_t> , T*
                              >::type to_boolean(T* v) const
  { return builder.CreateFPToUI(v, type<int>(), "fp_to_bool_tmp"); }

  // unary operation
  template<builder_fun1_t mem_fun>
  Value* operator()(unary_op<mem_fun>/* unused */, Value* a, char const*  name) const
  { return cast_result<unary_op<mem_fun> >((builder.*mem_fun)(a, name)); }

  // binary operations
  template<builder_fun2_t mem_fun>
  Value* operator()(binary_op<mem_fun> /* unused */
                    , Value* a1, Value* a2, char const* name) const
  { return cast_result<binary_op<mem_fun> >((builder.*mem_fun)(a1, a2, name)); }

  // return instruction
  ReturnInst* operator()(return_tag /* unused */, Value*  a) const 
  { return builder.CreateRet(a); }

  // variable assignment
  StoreInst* operator()(AllocaInst* variable, Value* value ) const
  { return builder.CreateStore(value, variable, false); }

  // reading a variable value
  Value* operator()(AllocaInst* variable) const
  {return builder.CreateLoad(variable);}

  // variable declaration
  AllocaInst* operator()(std::string const& name) const {
    AllocaInst* res(builder.CreateAlloca(type<value_t>(),0, name.c_str()));
    vars.add(name.begin(), name.end(), res);
    return res;
  }

  // if statement :
  // performs test and create then, else and end_if BasicBlock
  // returns <parent_function, else_BB, end_if_BB> to be used by else
  // and end_if statements
  control_flow_t operator()(if_tag /*unused*/, Value* expression) const{
    // get pointer to parent_function and create instruction blocks
    Function*  parent_function = builder.GetInsertBlock()->getParent();
    BasicBlock*  then_BB = BasicBlock::Create(ctx, " then", parent_function);
    BasicBlock*  else_BB = BasicBlock::Create(ctx," else");
    BasicBlock*  end_if_BB = BasicBlock::Create(ctx," end_if");
    // create test & branch instruction      
    // could use 
    // builder.CreateFCmpONE(expression,(*this)(static_cast<value_t>(0)), "if"))
    // for fp value_t instead of casting back to integral type
    builder.CreateCondBr(builder.CreateIsNull(to_boolean(expression), "if")
                         , else_BB, then_BB); 
    builder.SetInsertPoint(then_BB); // set then block and start using it
    // return data to be used for else block and end_if
    return control_flow_t(parent_function, then_BB, else_BB, end_if_BB);
  }

  // else statement : called even when there is no "else{...}" in
  // the code to close then block and start (possibly empty) else block 
  void operator()(else_tag /* unused */
                  , control_flow_t const & parent_then_else_endif) const {
    builder.CreateBr(fusn::at_c<3>(parent_then_else_endif));// jump to endif
    fusn::at_c<0>(parent_then_else_endif)
      ->getBasicBlockList().push_back(fusn::at_c<2>(parent_then_else_endif));
    builder.SetInsertPoint(fusn::at_c<2>(parent_then_else_endif));// set else block
  }

  void operator()(end_if_tag /*unused */
                  , Function* parent_function, BasicBlock* end_if_BB) const {
    builder.CreateBr(end_if_BB); // fall through to next block is mandatory with LLVM
    parent_function->getBasicBlockList().push_back(end_if_BB);// set end_if block
    builder.SetInsertPoint(end_if_BB); // and start using it
  }

  // while statement : creates blocks and set the stage for next
  // steps (condition, loop)
  // returns <parent_function, begin, condition_true, condition_false>
  control_flow_t operator()(while_begin_tag /*unused*/) const {
    // get pointer to parent_function and create instruction blocks
    Function* parent_function = builder.GetInsertBlock()->getParent();
    BasicBlock* while_begin_BB = BasicBlock::Create(ctx, " while_begin", parent_function);
    BasicBlock* while_is_true_BB = BasicBlock::Create(ctx," while_is_true");
    BasicBlock* while_is_false_BB = BasicBlock::Create(ctx," while_is_false");
    builder.CreateBr(while_begin_BB);//fall through to next block is mandatory with LLVM
    builder.SetInsertPoint(while_begin_BB);
    return control_flow_t(parent_function
                          , while_begin_BB, while_is_true_BB, while_is_false_BB);
  }
  // while condition: peforms branch according to test
  void operator()(while_condition_tag /*unused*/
                  , control_flow_t const& parent_begin_true_false
                  , Value* expression) const {
    // create test & branch instruction
    builder.CreateCondBr(builder.CreateIsNull(to_boolean(expression), "while_test")
                         , fusn::at_c<3>(parent_begin_true_false)
                         , fusn::at_c<2>(parent_begin_true_false)); 
    fusn::at_c<0>(parent_begin_true_false)
      ->getBasicBlockList().push_back(fusn::at_c<2>(parent_begin_true_false));
    builder.SetInsertPoint(fusn::at_c<2>(parent_begin_true_false));
  }

  // end of while statement : performs jump to begin of the while
  // (before test)
  void operator()(while_end_tag /* unused */
                  , control_flow_t const& parent_begin_true_false) const {
    builder.CreateBr(fusn::at_c<1>(parent_begin_true_false));// jump to begin
    fusn::at_c<0>(parent_begin_true_false)
      ->getBasicBlockList().push_back(fusn::at_c<3>(parent_begin_true_false));
    builder.SetInsertPoint(fusn::at_c<3>(parent_begin_true_false));// set end (false)
  }


  Value* operator()(end_ternary_tag /*unused*/
                    , control_flow_t const& p_t_e_e
		    , Value* then_v, Value* else_v) const {
    (*this)(end_if_tag(), fusn::at_c<0>(p_t_e_e), fusn::at_c<3>(p_t_e_e));
    llvm::PHINode* phi = builder.CreatePHI(type<value_t>(), "ternary_merge");
    phi->addIncoming(then_v, fusn::at_c<1>(p_t_e_e));
    phi->addIncoming(else_v, fusn::at_c<2>(p_t_e_e));
    return phi;
  }

  // constant values
  Value* operator()(short v) const 
  { return llvm::ConstantInt::get(ctx, llvm::APInt(sizeof(short)*8, v)); }
  Value* operator()(int v) const 
  { return llvm::ConstantInt::get(ctx, llvm::APInt(sizeof(int)*8, v)); }
  Value* operator()(long v) const 
  { return llvm::ConstantInt::get(ctx, llvm::APInt(sizeof(long)*8, v)); }
  Value* operator()(float v) const 
  { return llvm::ConstantFP::get(ctx, llvm::APFloat(v)); }// APFloat()
  Value* operator()(double v) const
  { return llvm::ConstantFP::get(ctx, llvm::APFloat(v)); }// is overloaded

  vars_t& vars;
  Builder& builder;
  llvm::LLVMContext& ctx;
};

language_3_grammar( Builder& b) 
  : language_3_grammar::base_type(program), build(builder_helper(vars, b)) {
  using qi::_val;
  using qi::_a;
  using qi::_1;
  using qi::_b;
  reserved_keywords = "var", "return", "if", "else";
  
  program =  code_block >> return_statement;
  code_block = *(variable_declaration | assignment | if_then_else | while_);

  // we want to enforce the space after "return"
  // so we must disable the skipper with lexeme[]
  return_statement = 
    qi::lexeme["return" >> standard::space]
    >> additive_expression [_val = build(return_tag(), _1)] 
    >> ';' ;

  if_then_else = qi::lit("if") 
    // build(if_tag, test_expression) returns
    // <parent_function, else_block, end_if_block>
    >> '(' >> expression [_a = build(if_tag(), _1)] >> ')'
    // build(else_tag, ...) must be called even when there
    // is no else clause to create an empty one as target
    // when test expression is false
    >> '{' >> code_block >> standard::char_('}') [build(else_tag(), _a)]
    >> -( qi::lit("else") >> '{' >> code_block >> '}' )
    // build(end_if_tag(), ...) must always be called
    >> qi::eps [build(end_if_tag(), boost::phoenix::at_c<0>(_a), boost::phoenix::at_c<3>(_a))] ;

  while_ = qi::lit("while") [_a=build(while_begin_tag())] 
    // build(while_tag, test_expression) returns
    // <parent_function, start_loop, end_loop>
    >> '(' >> expression [build(while_condition_tag(), _a, _1)] >> ')'
    >> '{' >> code_block >> standard::char_('}') [build(while_end_tag(), _a)];

  expression = ternary_expression [_val = _1] ;

  ternary_expression =  logical_or_expression [_val = _1]
    >> *(standard::char_('?') [_a=build(if_tag(), _val)]
         >> logical_or_expression [_b=_1]
	 >> standard::char_(':') [build(else_tag(), _a)] 
	 >> logical_or_expression [_val=build(end_ternary_tag(), _a, _b, _1)]);

  logical_or_expression = logical_and_expression[_val = _1]
    >> *("||" >> logical_and_expression [_val = build(logical_or_t(), _val, _1, "or_tmp")]);

  logical_and_expression = equality_expression[_val = _1]
    >> *("&&" >> equality_expression [_val = build(logical_and_t(), _val, _1, "and_tmp")]);

  equality_expression = compare_expression [_val = _1]
    >> *("==" >> logical_and_expression [_val = build(equality_t(), _val, _1, "eq_tmp")]
         | "!=" >> logical_and_expression [_val = build(inequality_t(), _val, _1, "ineq_tmp")]);

  compare_expression = additive_expression [_val = _1]
    >> *('<' >> additive_expression [_val = build(lesser_than_t(), _val, _1, "lt_tmp")]
         | '>' >> additive_expression [_val = build(greater_than_t(), _val, _1, "gt_tmp")]
         | "<=" >> additive_expression [_val = build(lesser_or_eq_t(), _val, _1, "le_tmp")]
         | ">=" >> additive_expression [_val = build(greater_or_eq_t(), _val, _1, "ge_tmp")]);

  additive_expression = multiplicative_expression [_val=_1]
    >> *(('+' >> multiplicative_expression [_val= build(add_t(), _val, _1,"addtmp")])
  	 |('-' >> multiplicative_expression [_val=build(sub_t(), _val, _1,"subtmp")]));

  multiplicative_expression = unary_expression [_val=_1]
    >> *(('*' >> unary_expression[_val= build(mul_t(), _val, _1, "multmp")])
         |('/' >> unary_expression [_val = build(div_t(), _val, _1, "divtmp")]));
  
  unary_expression = 
    primary_expression[_val = _1]
    | ('-' >> primary_expression[_val = build(neg_t(), _1, "negtmp")])
    | ('+' >> primary_expression[_val = _1]);

  primary_expression = 
    numeric_to_val [_val = _1]
    | id_declared_var [_val = build(_1)]
    | '(' >> ternary_expression  [_val = _1] >> ')' ;

  numeric_to_val = boost::spirit::traits::create_parser<value_t>::call()[_val = build(_1)];

  variable = id_declared_var[_val = build(_1)];

  //lexeme disables skipping for >>
  id_declaration %= qi::raw[qi::lexeme[standard::alpha >> *(standard::alnum | '_')]] ;

  // ditto for lexeme, id must be in vars
  // prevents partial match with only a prefix
  id_declared_var = qi::lexeme[ vars [_val = _1] >> !(standard::alnum | '_')];
  
  // disallow redeclaration of variables
  variable_declaration = "var" >> !id_declared_var
			       >> !reserved_keywords
			       >> id_declaration [_a = build(_1)]
			       >> (';' | '=' >> assignment_rhs(_a));

  // id_declared_var returns the AllocaInst* of the variable
  assignment = id_declared_var [_a = _1] >> '=' >> assignment_rhs(_a);
    
  assignment_rhs = expression[_a = _1] >> standard::char_(';')[build(qi::_r1, _a)];
}

qi::symbols<char, spirit::unused_type> reserved_keywords;
vars_t vars;
  
boost::phoenix::function<builder_helper> build;
  
qi::rule<Iterator, Value*(), standard::space_type> 
expression, logical_or_expression, logical_and_expression
  , equality_expression, compare_expression, additive_expression
  ,  multiplicative_expression, unary_expression, primary_expression
  , numeric_to_val, variable ;
qi::rule<Iterator, Value*(), qi::locals<control_flow_t, Value*>, standard::space_type>
ternary_expression;
qi::rule<Iterator, qi::locals<AllocaInst*>, standard::space_type> 
variable_declaration, assignment;
qi::rule<Iterator, AllocaInst*(), standard::space_type> id_declared_var;
qi::rule<Iterator, std::string(), standard::space_type> id_declaration;
qi::rule<Iterator, standard::space_type> program, code_block, return_statement;
qi::rule<Iterator, qi::locals<control_flow_t>, standard::space_type> if_then_else, while_;
qi::rule<Iterator, void(AllocaInst*), qi::locals<Value*>, standard::space_type> assignment_rhs;
};


template<typename V>
bool exec_function(llvm::Module& module, std::string const& function_name="main")
{
  static bool init_done(false);
  if(!init_done){
    llvm::InitializeNativeTarget();
    init_done= true;
  }
  llvm::FunctionPassManager fpm(&module);

  std::string ErrStr;
  llvm::ExecutionEngine* exec_engine_ptr= llvm::EngineBuilder(&module).setErrorStr(&ErrStr).create();
  if (!exec_engine_ptr) {
    std::cerr<<"Could not create ExecutionEngine:"<< ErrStr.c_str()<<std::endl;
    return false;
  }
#if EXAMPLE_OPTIM
  // lifted from kaleidoscope example :
  // http://www.llvm.org/docs/tutorial/LangImpl4.html#jit
  // Set up the optimizer pipeline.  Start with registering info
  // about how the target lays out data structures.
  fpm.add(new llvm::TargetData(*exec_engine_ptr->getTargetData()));
  // Do simple "peephole" optimizations and bit-twiddling optzns.
  fpm.add(llvm::createInstructionCombiningPass());
  // Reassociate expressions.
  fpm.add(llvm::createReassociatePass());
  // Eliminate Common SubExpressions.
  fpm.add(llvm::createGVNPass());
  // Simplify the control flow graph (deleting unreachable blocks, etc).
  fpm.add(llvm::createCFGSimplificationPass());
#else
  // as seen on http://www.remcobloemen.nl/2010/02/brainfuck-using-llvm/
  fpm.add(llvm::createInstructionCombiningPass()); // Cleanup for scalarrepl.
  fpm.add(llvm::createLICMPass());                 // Hoist loop invariants
  fpm.add(llvm::createIndVarSimplifyPass());       // Canonicalize indvars
  fpm.add(llvm::createLoopDeletionPass());         // Delete dead loops
   
  // Simplify code
  for(std::size_t repeat(0); repeat != 3; ++repeat) {
    fpm.add(llvm::createGVNPass());                  // Remove redundancies
    fpm.add(llvm::createSCCPPass());                 // Constant prop with SCCP
    fpm.add(llvm::createCFGSimplificationPass());    // Merge & remove BBs
    fpm.add(llvm::createInstructionCombiningPass());
    fpm.add(llvm::createAggressiveDCEPass());        // Delete dead instructions
    fpm.add(llvm::createCFGSimplificationPass());    // Merge & remove BBs
    fpm.add(llvm::createDeadStoreEliminationPass()); // Delete dead stores
  }
#endif
  fpm.doInitialization();
  fpm.run(*module.getFunction(function_name));

  std::cout<<"after optimization:\n";
  module.dump();

  typedef V (*fun_ptr_t)(void);
  fun_ptr_t fun_ptr = 
    reinterpret_cast<fun_ptr_t>(exec_engine_ptr->getPointerToFunction(module.getFunction(function_name)));
  std::cout<<"result: "<<(*fun_ptr)()<<std::endl;
  return true;
}

#ifdef NOFOLDER
typedef llvm::NoFolder folder_t; 
#else
typedef llvm::ConstantFolder folder_t; 
#endif

typedef llvm::IRBuilder<true, folder_t> builder_t;

int main(int argc, char* argv[]){
  typedef int value_t; // type used in arithmetic computations

  std::cin.unsetf(std::ios::skipws); //  Turn off white space skipping on the stream
  typedef std::string buffer_t;
  buffer_t buffer(std::istream_iterator<char>(std::cin), (std::istream_iterator<char>()));
  typedef buffer_t::const_iterator iter_t;
  iter_t iter(buffer.begin()), end(buffer.end());
  typedef language_3_grammar<value_t, iter_t, builder_t> grammar_t;
  llvm::Module module("lang_3", llvm::getGlobalContext());
  builder_t b(llvm::BasicBlock::Create(llvm::getGlobalContext(), "entry",
                                       llvm::cast<llvm::Function>(module.getOrInsertFunction("main"
                                                                                             , type<value_t>()
                                                                                             , NULL))));
  //TODO: ExecutionEngine::addGlobalMapping to bring extern functions
  // (e.g. a print function)
  grammar_t grammar(b);
  bool r = phrase_parse(iter, end, grammar, standard::space);// allow trailing spaces
  if (r && iter == end) {
    std::cout<<"parsing succeded !\n";
    llvm::verifyModule(module, llvm::PrintMessageAction);
    module.dump();
    exec_function<value_t>(module, "main");
  } else {
    std::string rest(iter, end);
    std::cerr << "parsing failed\n" << "stopped at: \"" << rest << "\"\n";
  }
  return r ? 0 : 1 ;
}

#define INSTANTIATE_IRBUILDER_UNOP(fn_)                                 \
  template Value* builder_t::fn_(llvm::Value* , llvm::Twine const &)

INSTANTIATE_IRBUILDER_UNOP(CreateNeg);
INSTANTIATE_IRBUILDER_UNOP(CreateFNeg);

#define INSTANTIATE_IRBUILDER_BINOP(fn_)                                \
  template Value* builder_t::fn_(llvm::Value* , Value* , llvm::Twine const &)

INSTANTIATE_IRBUILDER_BINOP(CreateOr);
INSTANTIATE_IRBUILDER_BINOP(CreateAnd);
INSTANTIATE_IRBUILDER_BINOP(CreateICmpSLT);
INSTANTIATE_IRBUILDER_BINOP(CreateAdd);
INSTANTIATE_IRBUILDER_BINOP(CreateMul);
INSTANTIATE_IRBUILDER_BINOP(CreateICmpNE);
INSTANTIATE_IRBUILDER_BINOP(CreateICmpSGT);
INSTANTIATE_IRBUILDER_BINOP(CreateSub);
INSTANTIATE_IRBUILDER_BINOP(CreateSDiv);
INSTANTIATE_IRBUILDER_BINOP(CreateICmpSLE);
INSTANTIATE_IRBUILDER_BINOP(CreateICmpSGE);
INSTANTIATE_IRBUILDER_BINOP(CreateFCmpOEQ);
INSTANTIATE_IRBUILDER_BINOP(CreateFCmpOLT);
INSTANTIATE_IRBUILDER_BINOP(CreateFCmpONE);
INSTANTIATE_IRBUILDER_BINOP(CreateFCmpOGT);
INSTANTIATE_IRBUILDER_BINOP(CreateFCmpOLE);
INSTANTIATE_IRBUILDER_BINOP(CreateFCmpOGE);
