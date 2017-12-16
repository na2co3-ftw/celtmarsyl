#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "celtmarsylJIT.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace llvm::orc;

static LLVMContext context;
static IRBuilder<> builder(context);
static std::unique_ptr<Module> module;
static std::unique_ptr<CeltmarsylJIT> jit;
static AllocaInst *f0, *f1, *f2, *f3;
static Value *famian;

const CmpInst::Predicate xtlo = CmpInst::ICMP_SLE;
const CmpInst::Predicate xylo = CmpInst::ICMP_SLT;
const CmpInst::Predicate clo = CmpInst::ICMP_EQ;
const CmpInst::Predicate xolo = CmpInst::ICMP_SGE;
const CmpInst::Predicate llo = CmpInst::ICMP_SGT;
const CmpInst::Predicate niv = CmpInst::ICMP_NE;

void ata(AllocaInst *dst, Value *srcValue) {
	Value* dstValue = builder.CreateLoad(dst);
	Value* res = builder.CreateAdd(dstValue, srcValue, "ata");
	builder.CreateStore(res, dst);
}
void ata(AllocaInst *dst, int src) {
	ata(dst, ConstantInt::get(Type::getInt32Ty(context), src, false));
}
void ata(AllocaInst *dst, AllocaInst *src) {
	ata(dst, builder.CreateLoad(src));
}

void nta(AllocaInst *dst, Value *srcValue) {
	Value* dstValue = builder.CreateLoad(dst);
	Value* res = builder.CreateSub(dstValue, srcValue, "nta");
	builder.CreateStore(res, dst);
}
void nta(AllocaInst *dst, int src) {
	nta(dst, ConstantInt::get(Type::getInt32Ty(context), src, false));
}
void nta(AllocaInst *dst, AllocaInst *src) {
	nta(dst, builder.CreateLoad(src));
}

void krz(AllocaInst *dst, Value *srcValue) {
	builder.CreateStore(srcValue, dst);
}
void krz(AllocaInst *dst, int src) {
	krz(dst, ConstantInt::get(Type::getInt32Ty(context), src, false));
}
void krz(AllocaInst *dst, AllocaInst *src) {
	krz(dst, builder.CreateLoad(src));
}

void inj(AllocaInst *a, AllocaInst *b, Value *cValue) {
	Value *bValue = builder.CreateLoad(b);
	builder.CreateStore(bValue, a);
	builder.CreateStore(cValue, b);
}
void inj(AllocaInst *a, AllocaInst *b, int c) {
	inj(a, b, ConstantInt::get(Type::getInt32Ty(context), c, false));
}
void inj(AllocaInst *a, AllocaInst *b, AllocaInst *c) {
	inj(a, b, builder.CreateLoad(c));
}

void fi(Value *left, Value *right, CmpInst::Predicate cond) {
	famian = builder.CreateICmp(cond, left, right, "fi");
}
void fi(AllocaInst *left, AllocaInst *right, CmpInst::Predicate cond) {
	fi(builder.CreateLoad(left), builder.CreateLoad(right), cond);
}
void fi(AllocaInst *left, int right, CmpInst::Predicate cond) {
	fi(builder.CreateLoad(left), ConstantInt::get(Type::getInt32Ty(context), right, false), cond);
}
void fi(int left, AllocaInst *right, CmpInst::Predicate cond) {
	fi(ConstantInt::get(Type::getInt32Ty(context), left, false), builder.CreateLoad(right), cond);
}
void fi(int left, int right, CmpInst::Predicate cond) {
	fi(ConstantInt::get(Type::getInt32Ty(context), left, false), ConstantInt::get(Type::getInt32Ty(context), right, false), cond);
}

using Label = BasicBlock*;

Label label(const Twine &name) {
	return BasicBlock::Create(context, name);
}

void nll(Label bb) {
	builder.CreateBr(bb);
	builder.GetInsertBlock()->getParent()->getBasicBlockList().push_back(bb);
	builder.SetInsertPoint(bb);
}

void krzXXc(Label bb) {
	builder.CreateBr(bb);
	BasicBlock *next = BasicBlock::Create(context, "", builder.GetInsertBlock()->getParent());
	builder.SetInsertPoint(next);
}

void malkrzXXc(Label bb) {
	BasicBlock *next = BasicBlock::Create(context, "", builder.GetInsertBlock()->getParent());
	builder.CreateCondBr(famian, bb, next);
	builder.SetInsertPoint(next);
}

void malkrz(AllocaInst *dst, Value *srcValue) {
	BasicBlock *then = BasicBlock::Create(context, "malkrz", builder.GetInsertBlock()->getParent());
	BasicBlock *next = BasicBlock::Create(context, "");
	builder.CreateCondBr(famian, then, next);
	builder.SetInsertPoint(then);
	krz(dst, srcValue);
	nll(next);
}
void malkrz(AllocaInst *dst, int src) {
	malkrz(dst, ConstantInt::get(Type::getInt32Ty(context), src, false));
}
void malkrz(AllocaInst *dst, AllocaInst *src) {
	malkrz(dst, builder.CreateLoad(src));
}

int main() {
	module = llvm::make_unique<Module>("jit", context);

	InitializeNativeTarget();
	InitializeNativeTargetAsmPrinter();
	InitializeNativeTargetAsmParser();
	jit = llvm::make_unique<CeltmarsylJIT>();
	module->setDataLayout(jit->getTargetMachine().createDataLayout());

	std::unique_ptr<legacy::FunctionPassManager> fpm = llvm::make_unique<legacy::FunctionPassManager>(module.get());
	fpm->add(createPromoteMemoryToRegisterPass());
	fpm->add(createInstructionCombiningPass());
	fpm->add(createReassociatePass());
	fpm->add(createGVNPass());
	fpm->add(createCFGSimplificationPass());
	fpm->doInitialization();

	FunctionType *fnty = FunctionType::get(Type::getInt32Ty(context), std::vector<Type *>(), false);
	Function *fn = Function::Create(fnty, Function::ExternalLinkage, "main", module.get());
	BasicBlock *bb = BasicBlock::Create(context, "entry", fn);
	builder.SetInsertPoint(bb);
	f0 = builder.CreateAlloca(Type::getInt32Ty(context), nullptr, "f0");
	f1 = builder.CreateAlloca(Type::getInt32Ty(context), nullptr, "f1");
	f2 = builder.CreateAlloca(Type::getInt32Ty(context), nullptr, "f2");
	f3 = builder.CreateAlloca(Type::getInt32Ty(context), nullptr, "f3");

	Label is = label("is");
	Label ka = label("ka");

	krz(f0, 12);
	krz(f1, 0);
	krz(f2, 1);
	nll(is); fi(f0, 0, clo); malkrzXXc(ka);
	nta(f0, 1);
	krz(f3, f1);
	ata(f3, f2);
	inj(f1, f2, f3);
	krzXXc(is);
	nll(ka); krz(f0, f1);

	builder.CreateRet(builder.CreateLoad(f0));
	verifyFunction(*fn);
	fpm->run(*fn);

	module->print(errs(), nullptr);

	auto h = jit->addModule(std::move(module));
	auto main = jit->findSymbol("main");
	assert(main && "Function not found");
	long (*builtFn)() = (long (*)())(intptr_t)cantFail(main.getAddress());
	printf("result:%ld\n", builtFn());

	return 0;
}
