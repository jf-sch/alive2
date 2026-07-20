// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/function.h"
#include "ir/instr.h"
#include "ir/constant.h"
#include "ir/globals.h"
#include "util/errors.h"
#include "util/hash.h"
#include "util/sort.h"
#include "util/unionfind.h"
#include <algorithm>
#include <fstream>
#include <set>
#include <unordered_set>
#include <bit>

using namespace smt;
using namespace util;
using namespace std;

namespace IR {



static IntType& get_int_type(uint64_t bits) {
  static std::unordered_map<uint64_t, std::unique_ptr<IntType>> type_map;
  if (!type_map.contains(bits)) {
    type_map.emplace(bits, make_unique<IntType>("i" + to_string(bits), bits));
  }
  return *type_map.at(bits);
}
static VectorType& get_vec_type(uint64_t elems, Type &ty) {
  static std::unordered_map<Type*, std::unordered_map<uint64_t, std::unique_ptr<VectorType>>> type_map;
  if (!type_map.contains(&ty)) {
    type_map.try_emplace(&ty);
  }
  auto &len_map = type_map.at(&ty);
  if (!len_map.contains(elems)) {
    len_map.emplace(elems, make_unique<VectorType>("v" + to_string(elems), elems, ty));
  }
  return *len_map.at(elems);
}



void BasicBlock::setInstrs(std::vector<std::unique_ptr<Instr>> &&instrs) {
  m_instrs = std::move(instrs);
}

std::unique_ptr<Instr>& BasicBlock::getInstr(size_t index) {
  return m_instrs.at(index);
}

expr BasicBlock::getTypeConstraints(const Function &f) const {
  expr t(true);
  for (auto &i : instrs()) {
    t &= i.getTypeConstraints(f);
  }
  return t;
}

void BasicBlock::fixupTypes(const Model &m) {
  for (auto &i : m_instrs) {
    i->fixupTypes(m);
  }
}

void BasicBlock::addInstr(unique_ptr<Instr> &&i, bool push_front) {
  if (push_front)
    m_instrs.emplace(m_instrs.begin(), std::move(i));
  else
    m_instrs.emplace_back(std::move(i));
}

void BasicBlock::addInstrAt(unique_ptr<Instr> &&i, const Instr *other,
                            bool before) {
  for (auto I = m_instrs.begin(); true; ++I) {
    assert(I != m_instrs.end());
    if (I->get() == other) {
      if (!before)
        ++I;
      m_instrs.emplace(I, std::move(i));
      break;
    }
  }
}

void BasicBlock::delInstr(const Instr *i) {
  for (auto I = m_instrs.begin(), E = m_instrs.end(); I != E; ++I) {
    if (I->get() == i) {
      m_instrs.erase(I);
      return;
    }
  }
}

void BasicBlock::popInstr() {
  m_instrs.pop_back();
}

void BasicBlock::addExitBlock(BasicBlock* bb) {
    exit_blocks.emplace(bb);
}

vector<Phi*> BasicBlock::phis() const {
  vector<Phi*> phis;
  for (auto &i : m_instrs) {
    if (auto phi = dynamic_cast<Phi*>(i.get()))
      phis.emplace_back(phi);
  }
  return phis;
}

JumpInstr::it_helper BasicBlock::targets() const {
  if (empty())
    return {};
  if (auto jump = dynamic_cast<JumpInstr*>(m_instrs.back().get()))
    return jump->targets();
  return {};
}

void BasicBlock::replaceTargetWith(const BasicBlock *from,
                                   const BasicBlock *to) {
  if (auto jump = dynamic_cast<JumpInstr*>(&this->back())) {
    jump->replaceTargetWith(from, to);
  }
}

unique_ptr<BasicBlock>
BasicBlock::dup(Function &f, const string &suffix) const {
  auto newbb = make_unique<BasicBlock>(name + suffix);
  for (auto &i : instrs()) {
    newbb->addInstr(i.dup(f, suffix));
  }
  return newbb;
}

void BasicBlock::rauw(const Value &what, Value &with) {
  for (auto &i : m_instrs) {
    i->rauw(what, with);
  }
}

void BasicBlock::transferInstrs(BasicBlock &tgt_bb) {
  tgt_bb.setInstrs(std::move(m_instrs));
  m_instrs.clear();
}

void BasicBlock::expandInlineFuncs(Function &f) {
  for (auto I = m_instrs.end(); I != m_instrs.begin();) {
    --I;
    if (auto call = dynamic_cast<InlineFuncCall*>(I->get())) {
      auto instrs_and_ret = call->replacementInstrs(f);
      auto &replace_instrs = instrs_and_ret.first;
      auto &replace_val = instrs_and_ret.second;
      for (auto &i: replace_instrs) {
        I = ++m_instrs.emplace(I, std::move(i));
      }
      f.rauw(*call, replace_val);
      I = m_instrs.erase(I);
    }
  }
}

ostream& operator<<(ostream &os, const BasicBlock &bb) {
  if (!bb.name.empty())
    os << string_view(bb.name).substr(1) << ":\n";
  for (auto &i : bb.instrs()) {
    os << "  ";
    i.print(os);
    os << '\n';
  }
  return os;
}


BasicBlock Function::sink_bb("#sink");

unsigned Function::FnDecl::hash() const {
  GenHash hash;

  function<void(const Type&)> hash_ty = [&](const Type &ty) {
    if (ty.isPtrType()) {
      hash.add((uint8_t)0x42);
    } else if (dynamic_cast<const VoidType*>(&ty)) {
      hash.add((uint8_t)0xEF);
    } else if (auto agg = ty.getAsAggregateType()) {
      hash.add((uint8_t)0x11);
      for (unsigned i = 0, e = agg->numElementsConst(); i != e; ++i) {
        if (!agg->isPadding(i))
          hash_ty(agg->getChild(i));
      }
    } else {
      uint8_t data[2] = { uint8_t(0x33+ty.isFloatType()), (uint8_t)ty.bits() };
      hash.add(data, sizeof(data));
    }
  };

  for (auto &[ty, attrs] : inputs) {
    hash_ty(*ty);
  }
  hash_ty(*output);
  hash.add(is_varargs * 32);
  return hash();
}

expr Function::getTypeConstraints() const {
  expr t(true);
  for (auto bb : getBBs()) {
    t &= bb->getTypeConstraints(*this);
  }
  for (auto &l : { getConstants(), getInputs(), getUndefs() }) {
    for (auto &v : l) {
      t &= v.getTypeConstraints();
    }
  }
  return t;
}

void Function::rauw(const Value &what, Value &with) {
  for (auto bb : getBBs())
    bb->rauw(what, with);
}

void Function::fixupTypes(const Model &m) {
  for (auto bb : getBBs()) {
    bb->fixupTypes(m);
  }
  for (auto &l : { getConstants(), getInputs(), getUndefs() }) {
    for (auto &v : l) {
      const_cast<Value&>(v).fixupTypes(m);
    }
  }
}

BasicBlock& Function::getEntryBB() {
  if (BB_order[0]->getName() == "#init") {
    return *BB_order[1];
  } else {
    return *BB_order[0];
  }
}

BasicBlock& Function::getBB(string_view name, bool push_front) {
  assert(name != "#sink");
  auto p = BBs.try_emplace(string(name), name);
  if (p.second) {
    if (push_front)
      BB_order.insert(BB_order.begin(), &p.first->second);
    else
      BB_order.push_back(&p.first->second);
  }
  return p.first->second;
}

const BasicBlock& Function::getBB(string_view name) const {
  assert(name != "#sink");
  return BBs.at(string(name));
}

const BasicBlock& Function::bbOf(const Instr &i) const {
  for (auto *bb : getBBs()) {
    for (auto &ii : bb->instrs())
      if (&ii == &i)
        return *bb;
  }
  UNREACHABLE();
}

BasicBlock& Function::insertBBAfter(string_view name, const BasicBlock &bb) {
  auto p = BBs.try_emplace(string(name), name);
  if (p.second) {
    auto I = find(BB_order.begin(), BB_order.end(), &bb);
    assert(I != BB_order.end());
    BB_order.insert(next(I), &p.first->second);
  }
  return p.first->second;
}

void Function::removeBB(BasicBlock &BB) {
  assert(BB.getName() != "#sink");
  BBs.erase(BB.getName());

  for (auto I = BB_order.begin(), E = BB_order.end(); I != E; ++I) {
    if (*I == &BB) {
      BB_order.erase(I);
      break;
    }
  }
}

void Function::addBBs(std::vector<std::unique_ptr<BasicBlock>> &&bbs) {
  std::vector<BasicBlock*> new_bbs;
  for (auto &src_bb : bbs) {
    auto &tgt_bb = getBB(src_bb->getName(), false);
    new_bbs.emplace_back(&tgt_bb);
    src_bb->transferInstrs(tgt_bb);
  }
  for (auto bb : getBBs()) {
    for (size_t i = 0; i < new_bbs.size(); i++) {
      bb->replaceTargetWith(bbs[i].get(), new_bbs[i]);
    }
  }
  topSort();
}

void Function::replaceTargetWith(const BasicBlock &from, const BasicBlock &to) {
  for (auto &pred : CFG::predBBs(*this, from)) {
    pred->replaceTargetWith(&from, &to);
  }
}

void Function::expandInlineFuncs() {
  for (auto bb : getBBs()) {
    bb->expandInlineFuncs(*this);
  }
}

void Function::addConstant(unique_ptr<Value> &&c) {
  constants.emplace_back(std::move(c));
}
IntConst& Function::getIntConst(int64_t val, Type &ty) {
  if (!int_const_map.contains(&ty)) {
    int_const_map.try_emplace(&ty);
  }
  auto &val_map = int_const_map.at(&ty);
  if (!val_map.contains(val)) {
    auto c = make_unique<IntConst>(ty, val);
    auto &c_ptr = *c;
    addConstant(std::move(c));
    val_map.emplace(val, &c_ptr);
  }
  return *val_map.at(val);
}
IntConst& Function::getIntConst(int64_t val, uint64_t bits) {
  return getIntConst(val, get_int_type(bits));
}
PoisonValue& Function::getPoison(Type &ty) {
  auto val = make_unique<PoisonValue>(ty);
  auto &ret = *val;
  addConstant(std::move(val));
  return ret;
}

Value* Function::getGlobalVar(string_view name) const {
  for (auto &c : constants) {
    if (c->getName() == name)
      return c.get();
  }
  return nullptr;
}

vector<GlobalVariable *> Function::getGlobalVars() const {
  vector<GlobalVariable *> gvs;
  for (auto I = constants.begin(), E = constants.end(); I != E; ++I) {
    if (auto *gv = dynamic_cast<GlobalVariable*>(I->get()))
      gvs.push_back(gv);
  }
  return gvs;
}

vector<string_view> Function::getGlobalVarNames() const {
  vector<string_view> gvnames;
  ranges::transform(
    getGlobalVars(), back_inserter(gvnames),
    [](auto &itm) { return string_view(itm->getName()).substr(1); });
  return gvnames;
}

void Function::addPredicate(unique_ptr<Predicate> &&p) {
  predicates.emplace_back(std::move(p));
}

void Function::addUndef(unique_ptr<UndefValue> &&u) {
  undefs.emplace_back(std::move(u));
}

void Function::addAggregate(unique_ptr<AggregateValue> &&a) {
  aggregates.emplace_back(std::move(a));
}

void Function::addInput(unique_ptr<Value> &&i) {
  assert(dynamic_cast<Input *>(i.get()) ||
         dynamic_cast<ConstantInput*>(i.get()));
  inputs.emplace_back(std::move(i));
}

void Function::replaceInput(std::unique_ptr<Value> &&c, unsigned idx) {
  inputs[idx] = std::move(c);
}

bool Function::hasReturn() const {
  for (auto &i : instrs()) {
    if (dynamic_cast<const Return *>(&i))
      return true;
  }
  return false;
}

void Function::syncDataWithSrc(Function &src) {
  auto IS = src.inputs.begin(), ES = src.inputs.end();
  auto IT = inputs.begin(), ET = inputs.end();

  for (; IS != ES && IT != ET; ++IS, ++IT) {
    if (auto in_tgt = dynamic_cast<Input*>(IT->get()))
      in_tgt->copySMTName(*dynamic_cast<Input*>(IS->get()));

    if (!(IS->get()->getType() == IT->get()->getType()).isTrue())
      throw AliveException("Source and target args have different type", false);
  }

  if (IS != ES || IT != ET)
    throw AliveException("Source and target have different number of args",
                         false);

  // copy function decls that are called indirectly
  auto copy_fns = [](const auto &src, auto &dst) {
    for (auto &c : src.getConstants()) {
      auto *gv = dynamic_cast<const GlobalVariable*>(&c);
      if (gv && gv->isArbitrarySize() && !dst.getGlobalVar(gv->getName()))
        dst.addConstant(make_unique<GlobalVariable>(*gv));
    }
  };
  copy_fns(src, *this);
  copy_fns(*this, src);

  for (auto &decl : fn_decls) {
    src.addFnDecl(FnDecl(decl));
  }
}

Function::instr_iterator::
instr_iterator(vector<BasicBlock*>::const_iterator &&BBI,
               vector<BasicBlock*>::const_iterator &&BBE)
  : BBI(std::move(BBI)), BBE(std::move(BBE)) {
  next_bb();
}

void Function::instr_iterator::next_bb() {
  if (BBI != BBE) {
    auto BB_instrs = (*BBI)->instrs();
    II = BB_instrs.begin();
    IE = BB_instrs.end();
  }
}

void Function::instr_iterator::operator++(void) {
  if (++II != IE)
    return;
  while (++BBI != BBE && (*BBI)->empty())
    ;
  next_bb();
}

static void add_users(Function::UsersTy &users, Value *i, BasicBlock *bb,
                      Value *val) {
  if (auto *agg = dynamic_cast<AggregateValue*>(val)) {
    for (auto elem : agg->getVals()) {
      add_users(users, val, bb, elem);
    }
  }
  if (i != val)
    users[val].emplace(i, bb);
}

void Function::addFnDecl(FnDecl &&decl) {
  if (find_if(fn_decls.begin(), fn_decls.end(),
      [&](auto &d) { return d.name == decl.name; }) != fn_decls.end())
    return;
  fn_decls.emplace_back(std::move(decl));
}

Function::UsersTy Function::getUsers() const {
  UsersTy users;
  for (auto *bb : getBBs()) {
    for (auto &i : bb->instrs()) {
      for (auto op : i.operands()) {
        add_users(users, const_cast<Instr*>(&i), bb, op);
      }
    }
  }
  for (auto &agg : aggregates) {
    add_users(users, agg.get(), nullptr, agg.get());
  }
  for (auto &c : constants) {
    if (auto agg = dynamic_cast<AggregateValue*>(c.get())) {
      add_users(users, agg, nullptr, agg);
    }
  }
  return users;
}

template <typename T>
static bool removeUnused(T &data, const Function::UsersTy &users,
                         const vector<string_view> &src_glbs) {
  bool changed = false;
  for (auto I = data.begin(); I != data.end(); ) {
    if (users.count(I->get())) {
      ++I;
      continue;
    }

    // don't delete glbs in target that are used in src
    if (auto gv = dynamic_cast<GlobalVariable*>(I->get())) {
      auto name = string_view(gv->getName()).substr(1);
      if (find(src_glbs.begin(), src_glbs.end(), name) != src_glbs.end()) {
        ++I;
        continue;
      }
    }

    I = data.erase(I);
    changed = true;
  }
  return changed;
}

bool Function::removeUnusedStuff(const UsersTy &users,
                                 const vector<string_view> &src_glbs) {
  bool changed = removeUnused(aggregates, users, src_glbs);
  changed |= removeUnused(constants, users, src_glbs);
  return changed;
}

static vector<BasicBlock*> top_sort(const vector<BasicBlock*> &bbs) {
  edgesTy edges(bbs.size());
  unordered_map<const BasicBlock*, unsigned> bb_map;

  unsigned i = 0;
  for (auto bb : bbs) {
    bb_map.emplace(bb, i++);
  }

  i = 0;
  for (auto bb : bbs) {
    for (auto &dst : bb->targets()) {
      auto dst_I = bb_map.find(&dst);
      if (dst_I != bb_map.end())
        edges[i].emplace(dst_I->second);
    }

    // If `bb` is a loop header, we need to go through its exit block
    // in order to account for some transitive dependencies we may have
    // missed due to compression of its inner loops.
    // If there are no inner loops, this is redundant and if `bb` is not
    // a loop header, the set of its exit blocks is empty. 
    for (auto &dst : bb->getExitBlocks()) {
      auto dst_I = bb_map.find(dst);
      if (dst_I != bb_map.end())
        edges[i].emplace(dst_I->second);
    }
    ++i;
  }

  vector<BasicBlock*> sorted_bbs;
  sorted_bbs.reserve(bbs.size());
  for (auto v : util::top_sort(edges)) {
    sorted_bbs.emplace_back(bbs[v]);
  }

  assert(sorted_bbs.size() == bbs.size());
  return sorted_bbs;
}

void Function::topSort() {
  BB_order = top_sort(BB_order);
}

static void
rauw_op(const unordered_map<const Value*,
                            vector<pair<BasicBlock*, Value*>>> &vmap,
        const unordered_set<const Value *> &phis_from_orig_bb,
        Value *i, Value *op) {
  auto it = vmap.find(op);
  if (it != vmap.end()) {
    // consider this case:
    //   loop:
    //     %op = phi ...
    //     %k  = phi [%op, %loop], ...
    //
    // In iteration i, %k should point to iteration (i-1)'s %k.
    // If is_phi_to_phi is true, %op is the phi in this block.
    bool is_phi_to_phi = dynamic_cast<const Phi *>(i) &&
                         phis_from_orig_bb.count(op);
    if (is_phi_to_phi) {
      if (it->second.size() >= 2) {
        i->rauw(*op, *it->second[it->second.size()-2].second);
      }
    } else {
      i->rauw(*op, *it->second.back().second);
    }
    return;
  }

  if (auto *agg = dynamic_cast<AggregateValue*>(op)) {
    for (auto &v : agg->getVals()) {
      rauw_op(vmap, phis_from_orig_bb, op, v);
    }
  }
}

static BasicBlock&
cloneBB(Function &F, const BasicBlock &BB, const char *suffix,
        const unordered_map<const BasicBlock*, vector<BasicBlock*>> &bbmap,
        unordered_map<const Value*, vector<pair<BasicBlock*, Value*>>> &vmap) {
  string bb_name = BB.getName() + suffix;
  auto &newbb = F.getBB(bb_name);
  unordered_set<const Value *> phis_from_orig_bb;

  for (auto &i : BB.instrs()) {
    if (dynamic_cast<const Phi *>(&i))
      phis_from_orig_bb.insert(&i);

    auto d = i.dup(F, suffix);
    for (auto &op : d->operands()) {
      rauw_op(vmap, phis_from_orig_bb, d.get(), op);
    }
    if (!i.isVoid())
      vmap[&i].emplace_back(&newbb, d.get());
    newbb.addInstr(std::move(d));
  }

  for (auto *phi : newbb.phis()) {
    for (auto &src : phi->sources()) {
      bool replaced = false;
      for (auto &[bb, copies] : bbmap) {
        if (src == bb->getName()) {
          phi->replaceSourceWith(src, copies.back()->getName());
          replaced = true;
          break;
        }
      }
      if (!replaced) {
        phi->removeValue(src);
      }
    }

    // If a phi becomes empty this can be a multi-entry loop without
    // loop-carried dependencies like:
    // loop:
    //   phi [x, entry1], [y, entry2]
    //   ...
    //   br loop
    if (phi->getValues().empty()) {
      for (auto &[val, copies] : vmap) {
        if (copies.back().second == phi) {
          newbb.rauw(*phi, *const_cast<Value*>(val));
          copies.pop_back();
          if (copies.empty())
            vmap.erase(val);
          break;
        }
      }
      newbb.delInstr(phi);
    }
  }

  return newbb;
}

static auto getPhiPredecessors(const Function &F) {
  unordered_map<string, vector<pair<Phi*, Value*>>> map;
  for (auto &i : F.instrs()) {
    if (auto phi = dynamic_cast<const Phi*>(&i)) {
      for (auto &[val, pred] : phi->getValues()) {
        map[pred].emplace_back(const_cast<Phi*>(phi), const_cast<Value*>(val));
      }
    }
  }
  return map;
}

void Function::unroll(unsigned k) {
  if (k == 0)
    return;

  LoopAnalysis la(*this);
  auto &roots = la.getRoots();
  if (roots.empty())
    return;

  auto &forest = la.getLoopForest();
  auto &sink = getSinkBB();

  vector<tuple<BasicBlock*, unsigned, bool>> worklist;
  // insert in reverse order because the worklist is iterated in LIFO
  for (auto I = roots.rbegin(), E = roots.rend(); I != E; ++I) {
    worklist.emplace_back(*I, 0, false);
  }

  // computed bottom-up during the post-order traversal below
  unordered_map<BasicBlock*, vector<BasicBlock*>> loop_nodes;

  // grab all value users before duplication so the list is shorter
  auto users = getUsers();
  auto phi_preds = getPhiPredecessors(*this);

  // traverse each loop tree in post-order
  while (!worklist.empty()) {
    auto [header, height, flag] = worklist.back();
    if (!flag) {
      get<2>(worklist.back()) = flag = true;
      auto I = forest.find(header);
      if (I != forest.end()) {
        // process all non-leaf children first
        for (auto *child : I->second) {
          if (forest.count(child))
            worklist.emplace_back(child, height+1, false);
        }
        continue;
      }
    }
    worklist.pop_back();

    vector<BasicBlock*> loop_bbs = { header };
    vector<BasicBlock*> own_loop_bbs = loop_bbs;
    auto I = forest.find(header);
    if (I != forest.end()) {
      for (auto *bb : top_sort(I->second)) {
        auto II = loop_nodes.find(bb);
        if (II != loop_nodes.end()) {
          loop_bbs.insert(loop_bbs.end(), II->second.begin(), II->second.end());
        } else {
          loop_bbs.emplace_back(bb);
        }
        own_loop_bbs.emplace_back(bb);
      }
    }

    // map: original BB -> {BB} U copies-of-BB
    unordered_map<const BasicBlock*, vector<BasicBlock*>> bbmap;
    for (auto *bb : loop_bbs) {
      bbmap[bb].emplace_back(bb);
    }

    // loop exit BB -> landing outside-loop BB
    set<pair<BasicBlock*, BasicBlock*>> exit_edges;
    for (auto *bb : loop_bbs) {
      for (auto &dst : bb->targets()) {
        if (!bbmap.count(&dst)) {
          exit_edges.emplace(bb, const_cast<BasicBlock*>(&dst));
          header->addExitBlock(const_cast<BasicBlock*>(&dst));
        }
      }
    }

    // Clone BBs
    // Note that the BBs list must be iterated in top-sort order so that
    // values from previous BBs are available in vmap
    auto &unrolled_bbs = loop_nodes.emplace(header, loop_bbs).first->second;
    unordered_map<const Value*, vector<pair<BasicBlock*, Value*>>> vmap;
    string name_prefix;
    for (unsigned i = 0; i < height; ++i) {
      name_prefix += "#1";
    }
    for (unsigned unroll = 2; unroll <= k; ++unroll) {
      string suffix = name_prefix + '#' + to_string(unroll);
      for (auto *bb : loop_bbs) {
        auto &copies = bbmap.at(bb);
        copies.emplace_back(&cloneBB(*this, *bb, suffix.c_str(), bbmap, vmap));
        unrolled_bbs.emplace_back(copies.back());
      }
    }

    // Clone the header once more so that the last iteration of the loop can
    // exit. Otherwise the last iteration would be wasted.
    // Here we assume the header is an exit, as that's the common case.
    // If not, this extra duplication is wasteful.
    if (bbmap.size() > 1) {
      auto &copies = bbmap.at(header);
      copies.emplace_back(&cloneBB(*this, *header, "#exit", bbmap, vmap));
      unrolled_bbs.emplace_back(copies.back());
    }

    // Patch jump targets
    for (auto &[bb, copies] : bbmap) {
      for (unsigned unroll = 0, e = copies.size(); unroll < e; ++unroll) {
        auto *cloned = copies[unroll];
        for (auto &tgt : cloned->targets()) {
          // Loop exit; no patching needed
          if (!bbmap.count(&tgt))
            continue;

          const BasicBlock *to = nullptr;
          auto &dst_vect = bbmap[&tgt];
          auto dst_unroll = dst_vect.size();

          // handle backedge
          if (&tgt == header) {
            to = unroll+1 < dst_unroll ? dst_vect[unroll + 1] : &sink;
          }
          // handle targets inside loop
          else {
            to = unroll < dst_unroll ? dst_vect[unroll] : &sink;
          }
          cloned->replaceTargetWith(&tgt, to);
        }
      }
    }

    // cache of introduced phis
    map<pair<const BasicBlock*, const Value*>, Phi*> new_phis;
    unsigned phi_counter = 0;

    topSort();
    DomTree dom_tree(*this, CFG(*this));

    auto bb_of = [&](const Value *val) {
      for (auto *bb : loop_bbs) {
        for (auto &instr : bb->instrs()) {
          if (val == &instr)
            return bb;
        }
      }
      UNREACHABLE();
    };

    // patch users outside of the loop
    for (auto &[val, copies] : vmap) {
      auto I = users.find(val);
      if (I == users.end())
        continue;

      BasicBlock *bb_val = bb_of(val);

      for (auto &[user, user_bb] : I->second) {
        // users inside the loop have been patched already
        if (bbmap.count(user_bb))
          continue;

        // insert a new phi on each dominator exit
        set<pair<BasicBlock*, Phi*>> added_phis;
        Phi *first_added_phi = nullptr;

        for (auto &[exit, dst] : exit_edges) {
          if (!dom_tree.dominates(bb_val, exit))
            continue;

          if (auto phi = dynamic_cast<Phi*>(user);
              phi && user_bb == dst) {
            // Check if the phi uses this value through this predecessor
            auto &vals = phi->getValues();
            auto *used_val = val;
            auto *ex = exit;
            if (!any_of(vals.begin(), vals.end(),
                        [&](const auto &p) {
                          return p.first == used_val && &getBB(p.second) == ex;
                        }))
              continue;

            auto &exit_copies = bbmap.at(exit);
            auto exit_I = exit_copies.begin(), exit_E = exit_copies.end();
            for (auto &[bb, val] : copies) {
              if (++exit_I == exit_E)
                break;
              phi->addValue(*val, string((*exit_I)->getName()));
            }
            continue;
          }

          auto &newphi = new_phis[make_pair(dst, val)];
          if (!newphi) {
            auto name = val->getName() + "#phi#" + to_string(phi_counter++);
            auto phi = make_unique<Phi>(val->getType(), std::move(name));
            newphi = phi.get();
            dst->addInstr(std::move(phi), true);
          }

          // we may have multiple edges from the loop into this BB
          // we need to duplicate the predecessor list for each of the
          // original incoming BB
          auto all_preds = newphi->sources();
          if (find(all_preds.begin(), all_preds.end(), exit->getName()) ==
                all_preds.end()) {
            newphi->addValue(*const_cast<Value*>(val), string(exit->getName()));
            auto &bb_dups = bbmap.at(exit);
            auto bb_I = bb_dups.begin(), bb_E = bb_dups.end();
            for (auto &[_, val] : copies) {
              if (++bb_I == bb_E)
                break;
              newphi->addValue(*val, string((*bb_I)->getName()));
            }
          }

          if (auto phi = dynamic_cast<Phi*>(user)) {
            for (auto &[pv, pred] : phi->getValues()) {
              if (pv == val && dom_tree.dominates(dst, &getBB(pred))){
                phi->replace(pred, *newphi);
              }
            }
          } else if (dynamic_cast<Instr*>(user)) {
            user->rauw(*val, *newphi);
            added_phis.emplace(dst, newphi);
            if (!first_added_phi)
              first_added_phi = newphi;
          }
        }

        // We have more than 1 dominating exit
        // add load/stores to avoid complex SSA building algorithms
        if (added_phis.size() > 1) {
          static PtrType ptr_type(0);
          static IntType i32(string("i32"), 32);
          auto &type = val->getType();
          auto size_alloc
            = make_unique<IntConst>(i32, Memory::getStoreByteSize(type));
          auto *size = size_alloc.get();
          addConstant(std::move(size_alloc));

          unsigned align = 16;
          auto name = val->getName() + "#ptr#" + to_string(phi_counter++);
          auto alloca = make_unique<Alloc>(ptr_type, string(name), *size,
                                           nullptr, align);

          auto store = [&](auto *bb, const auto *val) {
            bb->addInstrAt(make_unique<Store>(*alloca.get(),
                                              *const_cast<Value*>(val), align),
                           static_cast<const Instr*>(val), false);
          };

          store(bb_val, val);
          for (auto &[bb, val] : copies) {
            store(bb, val);
          }

          auto load
            = make_unique<Load>(type, name + "#load", *alloca.get(), align);
          auto *i = static_cast<Instr*>(user);
          i->rauw(*first_added_phi, *load.get());
          user_bb->addInstrAt(std::move(load), i, true);

          getFirstBB().addInstr(std::move(alloca), true);
        }
      }
    }

    // patch phis outside the loop with constant values
    for (auto *bb : own_loop_bbs) {
      auto I = phi_preds.find(bb->getName());
      if (I == phi_preds.end())
        continue;

      for (auto &[phi, val] : I->second) {
        if (!vmap.count(phi) && !vmap.count(val)) {
          for (auto *dup : bbmap.at(bb)) {
            // already in the phi
            if (dup == bb)
              continue;
            phi->addValue(*val, string(dup->getName()));
          }
        }
      }
    }
  }
}

void Function::print(ostream &os, bool print_header) const {
  if (!fn_decls.empty()) {
    for (auto &decl : fn_decls) {
      os << "declare " << *decl.output << ' ' << decl.name << '(';
      bool first = true;
      for (auto &input : decl.inputs) {
        if (!first)
          os << ", ";
        os << input.second << *input.first;
        first = false;
      }
      if (decl.is_varargs) {
        os << (first ? "..." : ", ...");
      }
      os << ')' << decl.attrs << '\n';
    }
    os << '\n';
  }

  {
    const auto &gvars = getGlobalVars();
    if (!gvars.empty()) {
      for (auto &v : gvars) {
        v->print(os);
        os << '\n';
      }
      os << '\n';
    }
  }

  if (print_header) {
    os << "define " << getType() << " @" << name << '(';
    bool first = true;
    for (auto &input : getInputs()) {
      if (!first)
        os << ", ";
      os << input;
      first = false;
    }
    if (isVarArgs())
      os << (first ? "..." : ", ...");
    os << ')' << attrs << " {\n";
  }

  bool first = true;
  for (auto bb : BB_order) {
    if (!first)
      os << '\n';
    os << *bb;
    first = false;
  }

  if (print_header)
    os << "}\n";
}

ostream& operator<<(ostream &os, const Function &f) {
  f.print(os);
  return os;
}

void Function::writeDot(const char *filename_prefix) const {
  string fname = getName();
  if (filename_prefix)
    fname += string(".") + filename_prefix;

  CFG cfg(*const_cast<Function*>(this));
  {
    ofstream file(fname + ".cfg.dot");
    cfg.printDot(file);
  }
  {
    ofstream file(fname + ".dom.dot");
    DomTree(*const_cast<Function*>(this), cfg).printDot(file);
  }
  {
    ofstream file(fname + ".looptree.dot");
    LoopAnalysis(*const_cast<Function*>(this)).printDot(file);
  }
}


void CFG::edge_iterator::next() {
  // jump to next BB with a terminator that is a jump
  while (true) {
    if (bbi == bbe)
      return;

    if (!(*bbi)->empty()) {
      if (auto instr = dynamic_cast<JumpInstr*>(&(*bbi)->back())) {
        ti = instr->targets().begin();
        te = instr->targets().end();
        return;
      }
    }
    ++bbi;
  }
}

CFG::edge_iterator::edge_iterator(vector<BasicBlock*>::iterator &&it,
                                  vector<BasicBlock*>::iterator &&end)
  : bbi(std::move(it)), bbe(std::move(end)) {
  next();
}

tuple<const BasicBlock&, const BasicBlock&, const Instr&>
  CFG::edge_iterator::operator*() const {
  return { **bbi, *ti, (*bbi)->back() };
}

void CFG::edge_iterator::operator++(void) {
  if (++ti == te) {
    ++bbi;
    next();
  }
}

bool CFG::edge_iterator::operator!=(edge_iterator &rhs) const {
  return bbi != rhs.bbi && (bbi == bbe || rhs.bbi == rhs.bbe || ti != rhs.ti);
}

std::vector<BasicBlock*> CFG::predBBs(Function &f, const BasicBlock &bb) {
  std::vector<BasicBlock*> pred_bbs;
  for (auto pred : f.getBBs()) {
    for (auto &curr_tgt : pred->targets()) {
      if (&curr_tgt == &bb) {
        pred_bbs.emplace_back(pred);
        break;
      }
    }
  }
  return pred_bbs;
}

static string_view bb_dot_name(const string &name) {
  if (name[0] == '%')
    return string_view(name).substr(1);
  return name;
}

void CFG::printDot(ostream &os) const {
  os << "digraph {\n"
        "\"" << bb_dot_name(f.getBBs()[0]->getName()) << "\" [shape=box];\n";

  for (auto [src, dst, instr] : *this) {
    os << '"' << bb_dot_name(src.getName()) << "\" -> \""
       << bb_dot_name(dst.getName()) << "\";\n";
  }
  os << "}\n";
}


// Relies on Alive's top_sort run during llvm2alive conversion in order to
// traverse the cfg in reverse postorder to build dominators.
void DomTree::buildDominators(const CFG &cfg) {
  // initialization
  // +1 for the sink BB
  unsigned i = f.getBBs().size() + 1;
  for (auto &b : f.getBBs()) {
    doms.emplace(b, *b).first->second.order = --i;
  }
  doms.emplace(&f.getSinkBB(), f.getSinkBB()).first->second.order = 0;

  // build predecessors relationship
  for (auto [src, tgt, instr] : cfg) {
    doms.at(&tgt).preds.push_back(&doms.at(&src));
  }

  auto &entry = doms.at(&f.getFirstBB());
  entry.dominator = &entry;

  // Cooper, Keith D.; Harvey, Timothy J.; and Kennedy, Ken (2001). 
  // A Simple, Fast Dominance Algorithm
  // http://www.cs.rice.edu/~keith/EMBED/dom.pdf
  // Makes multiple passes when CFG is cyclic to update incorrect initial
  // dominator guesses.
  bool changed;
  do {
    changed = false;
    for (auto &b : f.getBBs()) {
      auto &b_node = doms.at(b);
      if (b_node.preds.empty())
        continue;

      auto new_idom = b_node.preds.front();
      for (auto p : b_node.preds) {
        if (p->dominator != nullptr) {
          new_idom = intersect(p, new_idom);
        }
      }

      if (b_node.dominator != new_idom) {
        b_node.dominator = new_idom;
        changed = true;
      }
    }
  } while (changed);
}

DomTree::DomTreeNode* DomTree::intersect(DomTreeNode *f1, DomTreeNode *f2) {
  while (f1->order != f2->order) {
    while (f1->order < f2->order)
      f1 = f1->dominator;
    while (f2->order < f1->order)
      f2 = f2->dominator;
  }
  return f1;
}

// get immediate dominator BasicBlock
const BasicBlock* DomTree::getIDominator(const BasicBlock &bb) const {
  auto dom = doms.at(&bb).dominator;
  return dom ? &dom->bb : nullptr;
}

bool DomTree::dominates(const BasicBlock *a, const BasicBlock *b) const {
  auto *dom_a = &doms.at(a);
  auto *dom_b = &doms.at(b);
  // walk up the dominator tree of 'b' until we find 'a' or the function's entry
  while (true) {
    if (dom_b == dom_a)
      return true;
    if (dom_b == dom_b->dominator)
      break;
    dom_b = dom_b->dominator;
  }
  return false;
}

void DomTree::printDot(ostream &os) const {
  os << "digraph {\n"
        "\"" << bb_dot_name(f.getFirstBB().getName()) << "\" [shape=box];\n";

  for (auto I = f.getBBs().begin()+1, E = f.getBBs().end(); I != E; ++I) {
    if (auto dom = getIDominator(**I)) {
      os << '"' << bb_dot_name(dom->getName()) << "\" -> \""
         << bb_dot_name((*I)->getName()) << "\";\n";
    }
  }

  os << "}\n";
}


void LoopAnalysis::getDepthFirstSpanningTree() {
  // +1 to account for the sink BB
  unsigned bb_count = f.getBBs().size() + 1;
  node.resize(bb_count, nullptr);
  last.resize(bb_count, -1u);

  unsigned current = 0;
  vector<pair<BasicBlock*, bool>> worklist = { {&f.getFirstBB(), false} };
  unordered_set<const BasicBlock *> visited;
  while(!worklist.empty()) {
    auto &[bb, flag] = worklist.back();
    if (flag) {
      last[number[bb]] = current - 1;
      worklist.pop_back();
    } else {
      node[current] = bb;
      number[bb] = current++;
      flag = true;

      for (auto &tgt : bb->targets())
        if (visited.insert(&tgt).second)
          worklist.emplace_back(const_cast<BasicBlock*>(&tgt), false);
    }
  }
}

// Implementation of Tarjan-Havlak algorithm.
//
// Irreducible loops are partially supported.
//
// Tarjan, R. (1974). Testing Flow Graph Reducibility.
// Havlak, P. (1997). Nesting of reducible and irreducible loops.
void LoopAnalysis::run() {
  getDepthFirstSpanningTree();
  // +1 to account for the sink BB
  unsigned bb_count = f.getBBs().size() + 1;

  auto isAncestor = [this](unsigned w, unsigned v) -> bool {
    return w <= v && v <= last[w];
  };

  vector<set<unsigned>> nonBackPreds(bb_count), backPreds(bb_count);
  header.resize(bb_count, 0);
  type.resize(bb_count, NodeType::nonheader);

  for (auto [src, dst, instr] : cfg) {
    unsigned v = number.at(&src), w = number.at(&dst);
    if (isAncestor(w, v))
      backPreds[w].insert(v);
    else
      nonBackPreds[w].insert(v);
  }

  UnionFind uf(bb_count);

  for (unsigned w = bb_count - 1; w != -1u; --w) {
    set<unsigned> P;
    for (unsigned v : backPreds[w])
      if (v != w)
        P.insert(uf.find(v));
      else
        type[w] = NodeType::self;

    if (!P.empty())
      type[w] = NodeType::reducible;

    set<unsigned> workList(P);
    while (!workList.empty()) {
      auto I = workList.begin();
      unsigned x = *I;
      workList.erase(I);

      for (unsigned y : nonBackPreds[x]) {
        unsigned yy = uf.find(y);
        if (!isAncestor(w, yy)) {
          type[w] = NodeType::irreducible;
          nonBackPreds[w].insert(yy);
        } else if (yy != w && !P.count(yy)) {
          P.insert(yy);
          workList.insert(yy);
        }
      }
    }

    for (unsigned x : P) {
      header[x] = w;
      ENSURE(uf.merge(x, w) == w);
    }
  }

  // Construct the loop forest (0 or more loop trees)
  for (unsigned i = 0; i < bb_count; ++i) {
    auto h = header[i];
    if (h == 0 && type[i] != nonheader) {
      roots.emplace_back(node[i]);
      (void)forest[node[i]];
    }
    else if (h != 0 || type[i] != nonheader) {
      parent.emplace(node[i], node[h]);
      forest[node[h]].emplace_back(node[i]);
    }
  }
}

BasicBlock* LoopAnalysis::getParent(BasicBlock *bb) const {
  auto I = parent.find(bb);
  return I != parent.end() ? I->second : nullptr;
}

void LoopAnalysis::printDot(ostream &os) const {
  os << "digraph {\n";

  unordered_set<const BasicBlock*> seen_roots;
  auto decl_root = [&](const BasicBlock *root) {
    auto name = bb_dot_name(root->getName());
    if (seen_roots.insert(root).second)
      os << '"' << name << "\" [shape=square];\n";
    return name;
  };

  for (auto &[root, nodes] : forest) {
    auto root_name = decl_root(root);
    for (auto *node : nodes) {
      os << '"' << root_name << "\" -> \""
         << bb_dot_name(node->getName()) << "\";\n";
    }
  }
  os << "}\n";
}





std::unique_ptr<InlineFunc> Map::get_lambda_template(Type &ret_type, Type &idx_type, LambdaArgs lambda_args) {
  auto lambda = make_unique<InlineFunc>(ret_type, "lambda");
  if (lambda_args & Idx) {
    lambda->addParam(make_unique<InlineFuncParam>(idx_type, "idx"));
  }
  if (lambda_args & Elem) {
    lambda->addParam(make_unique<InlineFuncParam>(ret_type, "elem"));
  }
  return lambda;
}

std::vector<Value*> Map::operands() const {
  std::vector<Value*> ops = {lambda};
  for (auto op : {ptr, stop_idx}) {
    ops.emplace_back(op);
  }
  return ops;
}

unique_ptr<Map> Map::dup(Function &f, const std::string &suffix) const {
  return make_unique<Map>(name + suffix, unroll_cnt, *ptr, align, *stop_idx, *lambda, lambda_args, gep_inbounds, gep_nusw, gep_nuw);
}

void Map::rauw(const Value &what, Value &with) {
  if (lambda == &what) {
    auto new_lambda = dynamic_cast<InlineFunc*>(&with);
    assert(new_lambda != nullptr);
    lambda = new_lambda;
  }
  for (auto op : {ptr, stop_idx}) {
    RAUW(op);
  }
}



std::tuple<std::vector<std::unique_ptr<BasicBlock>>, BasicBlock&, Value&> Map::unrollIdx(Function &f, const BasicBlock &next_bb) const {
  std::vector<std::unique_ptr<BasicBlock>> replace_bbs;
  const auto prefix = name + '_';
  auto &idx_ty = getIdxType();

  auto loop_entry = make_unique<BasicBlock>(prefix + "loop_entry");
  auto loop = make_unique<BasicBlock>(prefix + "loop_unroll_idx");
  loop_entry->addInstr(make_unique<Branch>(*loop));

  auto prev_idx = make_unique<Phi>(idx_ty, prefix + "prev_idx");
  prev_idx->addValue(f.getIntConst(-1, idx_ty), std::string(loop_entry->getName()));
  auto idx = make_unique<BinOp>(idx_ty, prefix + "idx", *prev_idx, f.getIntConst(1, idx_ty), BinOp::Op::Add);
  prev_idx->addValue(*idx, std::string(loop->getName()));
  auto cmp = make_unique<ICmp>(get_int_type(1), prefix + "eq_len", ICmp::Cond::EQ, *idx, *stop_idx);
  auto br_cond = make_unique<Branch>(*cmp, next_bb, *loop);

  Value &len = *idx;
  loop->addInstr(std::move(prev_idx));
  loop->addInstr(std::move(idx));
  loop->addInstr(std::move(cmp));
  loop->addInstr(std::move(br_cond));
  BasicBlock &entry = *loop_entry;
  replace_bbs.emplace_back(std::move(loop_entry));
  replace_bbs.emplace_back(std::move(loop));
  return {std::move(replace_bbs), entry, len};
}

std::pair<std::vector<std::unique_ptr<BasicBlock>>, BasicBlock&> Map::replacementBBsMemset(Function &f, const BasicBlock &next_bb) const {
  auto &elem_ty = lambda->getType();
  assert(lambda_args == None && elem_ty.isIntType() && elem_ty.bits() == bits_byte);

  std::vector<std::unique_ptr<BasicBlock>> replace_bbs;
  const auto prefix = name + '_';
  auto bb = make_unique<BasicBlock>(prefix + "memset");
  auto val = make_unique<InlineFuncCall>(prefix + "get_val", std::vector<Value*>{}, *lambda);
  auto memset = make_unique<Memset>(*ptr, *val, *stop_idx, align, TailCallInfo{.type = TailCallInfo::Tail});

  bb->addInstr(std::move(val));
  bb->addInstr(std::move(memset));
  bb->addInstr(make_unique<Branch>(next_bb));
  BasicBlock &entry = *bb;
  replace_bbs.emplace_back(std::move(bb));
  return {std::move(replace_bbs), entry};
}



std::pair<std::vector<std::unique_ptr<BasicBlock>>, BasicBlock&> Map::replacementBBsSingleStore(Function &f, const BasicBlock &next_bb) const {
  auto &elem_ty = lambda->getType();
  if (lambda_args == None && elem_ty.isIntType() && elem_ty.bits() == bits_byte) {
    return replacementBBsMemset(f, next_bb);
  }

  std::vector<std::unique_ptr<BasicBlock>> replace_bbs;
  const auto prefix = name + '_';
  auto &bool_ty = get_int_type(1);
  auto &stop_idx_ty = stop_idx->getType();
  auto &sink = f.getSinkBB();

  BasicBlock *prev_cond;
  {
    const uint64_t len = 0;
    const auto suffix = '#' + to_string(len);
    auto cond = make_unique<BasicBlock>(prefix + "cond" + suffix);
    auto cmp = make_unique<ICmp>(bool_ty, prefix + "eq_len" + suffix, ICmp::Cond::EQ, *stop_idx, f.getIntConst(0, stop_idx_ty));
    auto br_cond = make_unique<Branch>(*cmp, next_bb, sink);
    cond->addInstr(std::move(cmp));
    cond->addInstr(std::move(br_cond));
    prev_cond = cond.get();
    replace_bbs.emplace_back(std::move(cond));
  }
  auto &entry = *prev_cond;

  std::vector<Value*> elems;
  for (uint64_t len = 1; len < unroll_cnt + 1; len++) {
    const uint64_t idx = len - 1;
    const auto suffix = '#' + to_string(len);
    auto cond = make_unique<BasicBlock>(prefix + "cond" + suffix);
    auto map_len = make_unique<BasicBlock>(prefix + "map_len" + suffix);
    prev_cond->replaceTargetWith(&sink, cond.get());

    std::vector<Value*> args;
    if (lambda_args & Idx) {
      args.emplace_back(&f.getIntConst(idx, lambda->paramTypeAt(args.size())));
    }
    if (lambda_args & Elem) {
      auto elem_gep = make_unique<GEP>(ptr->getType(), prefix + "elem_gep" + suffix, *ptr, gep_inbounds, gep_nusw, gep_nuw);
      elem_gep->addIdx(elem_ty, f.getIntConst(idx, bits_for_offset));
      auto load_elem = make_unique<Load>(elem_ty, prefix + "load_elem" + suffix, *elem_gep, align);
      args.emplace_back(load_elem.get());
      cond->addInstr(std::move(elem_gep));
      cond->addInstr(std::move(load_elem));
    }
    auto map_elem = make_unique<InlineFuncCall>(prefix + "map_elem" + suffix, std::move(args), *lambda);
    elems.emplace_back(map_elem.get());
    cond->addInstr(std::move(map_elem));

    auto cmp = make_unique<ICmp>(bool_ty, prefix + "eq_len" + suffix, ICmp::Cond::EQ, *stop_idx, f.getIntConst(len, stop_idx_ty));
    auto br_cond = make_unique<Branch>(*cmp, *map_len, sink);
    cond->addInstr(std::move(cmp));
    cond->addInstr(std::move(br_cond));

    auto vec_gep = make_unique<GEP>(ptr->getType(), "vec_gep", *ptr, gep_inbounds, gep_nusw, gep_nuw);
    vec_gep->addIdx(get_vec_type(elems.size(), elem_ty), f.getIntConst(0, bits_for_offset));
    auto store_vec = make_unique<StoreMultiple>(*vec_gep, elem_ty, std::vector(elems), align);
    map_len->addInstr(std::move(vec_gep));
    map_len->addInstr(std::move(store_vec));
    map_len->addInstr(make_unique<Branch>(next_bb));

    prev_cond = cond.get();
    replace_bbs.emplace_back(std::move(cond));
    replace_bbs.emplace_back(std::move(map_len));
  }
  return {std::move(replace_bbs), entry};
}

std::pair<std::vector<std::unique_ptr<BasicBlock>>, BasicBlock&> Map::replacementBBsBinTree(Function &f, const BasicBlock &next_bb) const {
  auto &elem_ty = lambda->getType();
  if (lambda_args == None && elem_ty.isIntType() && elem_ty.bits() == bits_byte) {
    return replacementBBsMemset(f, next_bb);
  }

  std::vector<std::unique_ptr<BasicBlock>> replace_bbs;
  const auto prefix = name + '_';
  auto &bool_ty = get_int_type(1);
  auto &stop_idx_ty = stop_idx->getType();
  const uint64_t unroll_cnt_bit_floor = std::bit_floor(unroll_cnt);
  const uint64_t leaf_tree_nodes = unroll_cnt_bit_floor << 1u;

  auto unroll_cond = make_unique<BasicBlock>(prefix + "unroll_cond");
  auto bit_checks_bb = make_unique<BasicBlock>(prefix + "bit_checks");
  auto leq_unroll_cnt = make_unique<ICmp>(bool_ty, prefix + "leq_unroll_cnt", ICmp::Cond::ULE, *stop_idx, f.getIntConst(unroll_cnt, stop_idx_ty));
  auto br_unroll_cond = make_unique<Branch>(*leq_unroll_cnt, *bit_checks_bb, f.getSinkBB());
  unroll_cond->addInstr(std::move(leq_unroll_cnt));
  unroll_cond->addInstr(std::move(br_unroll_cond));

  uint64_t curr_tree_nodes = leaf_tree_nodes;
  curr_tree_nodes >>= 1u;
  std::unordered_map<uint64_t, Value*> bit_checks;
  std::unordered_map<uint64_t, std::unordered_map<uint64_t, const BasicBlock*>> tree_nodes_len_idx;
  tree_nodes_len_idx.try_emplace(0);
  for (uint64_t idx = 0; idx < unroll_cnt + 1; idx++) {
    tree_nodes_len_idx.at(0).emplace(idx, &next_bb);
  }
  for (uint64_t curr_pow2 = 1; curr_pow2 < unroll_cnt_bit_floor + 1; curr_pow2 <<= 1u) {
    tree_nodes_len_idx.try_emplace(curr_pow2);
    const auto suffix = '#' + to_string(curr_pow2);

    for (uint64_t curr_node = 0; curr_node < curr_tree_nodes; curr_node++) {
      const uint64_t base_idx = curr_node * (curr_pow2 << 1u);
      if (base_idx + curr_pow2 > unroll_cnt) {
        break;
      }
      const auto suffix2 = suffix + '#' + to_string(curr_node);
      auto cond = make_unique<BasicBlock>(prefix + "cond" + suffix2);
      auto map_range = make_unique<BasicBlock>(prefix + "map_range" + suffix2);

      if (!bit_checks.contains(curr_pow2)) {
        auto and_pow2 = make_unique<BinOp>(stop_idx_ty, prefix + "and" + suffix2, *stop_idx, f.getIntConst(curr_pow2, stop_idx_ty), BinOp::Op::And);
        auto bit_cmp = make_unique<ICmp>(bool_ty, prefix + "eq_zero" + suffix2, ICmp::Cond::EQ, *and_pow2, f.getIntConst(0, stop_idx_ty));
        bit_checks.emplace(curr_pow2, bit_cmp.get());
        bit_checks_bb->addInstr(std::move(and_pow2));
        bit_checks_bb->addInstr(std::move(bit_cmp));
      }
      auto br_cond = make_unique<Branch>(*bit_checks.at(curr_pow2), *tree_nodes_len_idx.at(curr_pow2 >> 1u).at(base_idx), *map_range);
      cond->addInstr(std::move(br_cond));

      std::vector<Value*> elems;
      for (uint64_t vec_idx = 0; vec_idx < curr_pow2; vec_idx++) {
        const auto suffix3 = suffix2 + '#' + to_string(vec_idx);
        const uint64_t idx = base_idx + vec_idx;

        std::vector<Value*> args;
        if (lambda_args & Idx) {
          args.emplace_back(&f.getIntConst(idx, lambda->paramTypeAt(args.size())));
        }
        if (lambda_args & Elem) {
          auto elem_gep = make_unique<GEP>(ptr->getType(), prefix + "elem_gep" + suffix3, *ptr, gep_inbounds, gep_nusw, gep_nuw);
          elem_gep->addIdx(elem_ty, f.getIntConst(idx, bits_for_offset));
          auto load_elem = make_unique<Load>(elem_ty, prefix + "load_elem" + suffix3, *elem_gep, align);
          args.emplace_back(load_elem.get());
          map_range->addInstr(std::move(elem_gep));
          map_range->addInstr(std::move(load_elem));
        }
        auto map_elem = make_unique<InlineFuncCall>(prefix + "map_elem" + suffix3, std::move(args), *lambda);
        elems.emplace_back(map_elem.get());
        map_range->addInstr(std::move(map_elem));
      }
      auto vec_gep = make_unique<GEP>(ptr->getType(), "vec_gep", *ptr, gep_inbounds, gep_nusw, gep_nuw);
      vec_gep->addIdx(elem_ty, f.getIntConst(base_idx, bits_for_offset));
      vec_gep->addIdx(get_vec_type(elems.size(), elem_ty), f.getIntConst(0, bits_for_offset));
      auto store_vec = make_unique<StoreMultiple>(*vec_gep, elem_ty, std::vector(elems), align);
      map_range->addInstr(std::move(vec_gep));
      map_range->addInstr(std::move(store_vec));

      const uint64_t next_idx = base_idx + curr_pow2;
      uint64_t next_len = std::min(curr_pow2 >> 1u, std::bit_floor(unroll_cnt - next_idx));
      map_range->addInstr(make_unique<Branch>(*tree_nodes_len_idx.at(next_len).at(next_idx)));
      tree_nodes_len_idx.at(curr_pow2).emplace(base_idx, cond.get());
      replace_bbs.emplace(replace_bbs.begin(), std::move(map_range));
      replace_bbs.emplace(replace_bbs.begin(), std::move(cond));
    }
    curr_tree_nodes >>= 1u;
  }

  auto &entry = *unroll_cond;
  bit_checks_bb->addInstr(make_unique<Branch>(*tree_nodes_len_idx.at(unroll_cnt_bit_floor).at(0)));
  replace_bbs.emplace(replace_bbs.begin(), std::move(bit_checks_bb));
  replace_bbs.emplace(replace_bbs.begin(), std::move(unroll_cond));
  return {std::move(replace_bbs), entry};
}

std::pair<std::vector<std::unique_ptr<BasicBlock>>, BasicBlock&> Map::replacementBBsAliasAware(Function &f, const BasicBlock &next_bb) const {
  auto &elem_ty = lambda->getType();
  if (lambda_args == None && elem_ty.isIntType() && elem_ty.bits() == bits_byte) {
    return replacementBBsMemset(f, next_bb);
  }

  std::vector<std::unique_ptr<BasicBlock>> replace_bbs;
  const auto prefix = name + '_';
  auto &bool_ty = get_int_type(1);
  auto &stop_idx_ty = stop_idx->getType();
  auto &sink = f.getSinkBB();

  BasicBlock *prev_map;
  {
    const uint64_t len = 0;
    const auto suffix = '#' + to_string(len);
    auto cond = make_unique<BasicBlock>(prefix + "cond" + suffix);
    auto cmp = make_unique<ICmp>(bool_ty, prefix + "eq_len" + suffix, ICmp::Cond::EQ, *stop_idx, f.getIntConst(0, stop_idx_ty));
    auto br_cond = make_unique<Branch>(*cmp, next_bb, sink);
    cond->addInstr(std::move(cmp));
    cond->addInstr(std::move(br_cond));
    prev_map = cond.get();
    replace_bbs.emplace_back(std::move(cond));
  }
  auto &entry = *prev_map;

  const BasicBlock *prev_store = &next_bb;
  for (uint64_t len = 1; len < unroll_cnt + 1; len++) {
    const uint64_t idx = len - 1;
    const auto suffix = '#' + to_string(len);
    auto map_bb = make_unique<BasicBlock>(prefix + "map" + suffix);
    auto store_bb = make_unique<BasicBlock>(prefix + "store" + suffix);
    prev_map->replaceTargetWith(&sink, map_bb.get());

    auto elem_gep = make_unique<GEP>(ptr->getType(), prefix + "elem_gep" + suffix, *ptr, gep_inbounds, gep_nusw, gep_nuw);
    elem_gep->addIdx(elem_ty, f.getIntConst(idx, bits_for_offset));
    GEP &gep = *elem_gep;
    map_bb->addInstr(std::move(elem_gep));

    std::vector<Value*> args;
    if (lambda_args & Idx) {
      args.emplace_back(&f.getIntConst(idx, lambda->paramTypeAt(args.size())));
    }
    if (lambda_args & Elem) {
      auto load_elem = make_unique<Load>(elem_ty, prefix + "load_elem" + suffix, gep, align);
      args.emplace_back(load_elem.get());
      map_bb->addInstr(std::move(load_elem));
    }
    auto map_elem = make_unique<InlineFuncCall>(prefix + "map_elem" + suffix, std::move(args), *lambda);
    Value &elem = *map_elem;
    map_bb->addInstr(std::move(map_elem));

    auto cmp = make_unique<ICmp>(bool_ty, prefix + "eq_len" + suffix, ICmp::Cond::EQ, *stop_idx, f.getIntConst(len, stop_idx_ty));
    auto br_cond = make_unique<Branch>(*cmp, *store_bb, sink);
    map_bb->addInstr(std::move(cmp));
    map_bb->addInstr(std::move(br_cond));

    auto store_vec = make_unique<Store>(gep, elem, align);
    store_bb->addInstr(std::move(store_vec));
    store_bb->addInstr(make_unique<Branch>(*prev_store));

    prev_map = map_bb.get();
    prev_store = store_bb.get();
    replace_bbs.emplace_back(std::move(map_bb));
    replace_bbs.emplace_back(std::move(store_bb));
  }
  return {std::move(replace_bbs), entry};
}

std::ostream& operator<<(std::ostream &os, const Map &m) {
  os << "map " << m.getPtr() << " align " << m.getAlign() << " [" << '0' << ':' << m.getStopIdx() << ':' << '1' << "]\n " << m.getLambda().getName();
  return os;
}

}
