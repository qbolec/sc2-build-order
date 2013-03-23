//WYMAGA -fno-strict-aliasing bo nie umiem lepiej napisaæ alokatora

//#define HASH_MAP_HISTORY
#include<vector>
#include<map>
#include<set>
#include<string>
#include<iostream>
#include<algorithm>
using namespace std;
#define foreach(c,it) for(typeof((c).begin()) it=(c).begin();it!=(c).end();++it)
typedef unsigned int uint32;
typedef int int32;
typedef short int int16;
typedef unsigned short int uint16;
typedef char int8;
typedef unsigned char uint8;
#include<ext/slist>
#include<ext/hash_map>
#include<ext/hash_set>
using namespace __gnu_cxx;
const uint32 VERBOSITY_LEVEL = 20;
#include"../tracer.h"
#include"slabocator.hpp"
typedef int8 Value;
typedef uint32 VariableId;
typedef uint32 Time;

const uint32 SLAB_SIZE=1000000;
Slabocator<1200,SLAB_SIZE> slabocator;
void * operator new (size_t s){
  if(s<=SLAB_SIZE){
    return slabocator.allocate(s);
  }else{
    ctrace << "allocating " << s << endl;
    ctrace.enter();
    void *p = malloc(s);
    if(NULL==p){
      cerr << "failed to allocate " << s << " bytes" << endl;
      exit(-1);
    }
    ctrace.leave();
    return p;
  } 
}
void operator delete(void *p){
  if(slabocator.contains(p)){
    slabocator.free(p);
  }else{
    //ctrace << "deallocation" << endl;
    free(p);
  }
}

Value readValue(istream & sin){
  int32 x;
  sin >> x;
  assert(0<=x);
  
  return x;
}

class NameToId {
  map<string,VariableId> mapping;
  vector<string> unmapping;
  VariableId free_id;
public:
  NameToId():free_id(0){}
  void declare(string name){
    assert(mapping.find(name)==mapping.end());
    mapping[name]=free_id++;
    unmapping.push_back(name);
  }
  VariableId map(string name){
    if(mapping.find(name)==mapping.end()){
      cerr << "unknown variable " << name << endl;
      throw 42;
    }
    return mapping[name];
  }
  string unmap(VariableId id){
    return unmapping[id];
  }
};
NameToId name_to_id;//fuj!

class Variable{
  VariableId id;
public:
  Variable(VariableId id):id(id){}
  Variable(string name):id(name_to_id.map(name)){}
  Variable(istream & sin){
    string name;
    sin >> name;
    id = name_to_id.map(name);
  }
  VariableId get_id()const{
    return id;
  }
  string get_name()const{
    return name_to_id.unmap(id);
  }
};
ostream & operator << (ostream & sout,const Variable &variable){
  return sout << variable.get_name();
}



class Domination{
private:
  vector<int32> up;
public:
  int32 go_up(const uint32 id)const{
    return up[id];
    //return id < up.size() ? up[id] : -1;
  }
  Domination (istream & sin):up(256,-1){
    uint32 m;
    sin >> m;
    set<uint32> seen;
    
    for(uint32 i=0;i<m;++i){
      Variable lower(sin);
      Variable higher(sin);
      uint32 lower_id=lower.get_id();
      assert(seen.insert(lower_id).second);
      //chodzi o to, ¿eby sortowanie topologiczne by³o zgodne z lexykograficznym
      //w takim sensie, ¿eby sortuj¹c wektory od najmniejszego do najwiêkszego leksykograficznie
      //relacja dominacji zachodzi³a tylko w jedn¹ stronê (w prawo)
      //czyli: jeœli wektor v dominuje wektor u, tzn ¿e v jest po u w porz¹dku leksykograficznym,
      //gdyby bowiem by³ wczeœniej, to znaczy³oby ¿e pierwsza pozycja k na której siê ró¿ni¹ spe³nia
      // v[k] < u[k], ale wtedy jakim cudem v dominuje u? musia³by u¿yæ "mocniejszych" zmiennych,
      //ale one wszystkie s¹ na lewo od k.
      assert(higher.get_id()<lower.get_id());
      up[lower_id]=higher.get_id();
    }
    
  }
};


class State{
  const static uint32 LEN=42;
  Value valuation[LEN];
public:
  bool operator ==(const State & other)const{
    return !memcmp(valuation,other.valuation,sizeof(valuation));
  }
  bool operator !=(const State & other)const{
    return !(*this == other);
  }
  bool operator <(const State & other)const{
    return memcmp(valuation,other.valuation,sizeof(valuation))<0;
  }
  Value get_value(const Variable &variable)const{
    const VariableId id=variable.get_id();
    assert(id<LEN);
    return valuation[id];
  }
  void set_value(const Variable &variable,Value new_value){
    if(new_value<0){
      static bool reported[256]={};
      if(!reported[variable.get_id()]){
        cerr << "assigning " << (int32)new_value <<" value for " << variable << endl;
        reported[variable.get_id()]=true;
      }
    }
    const VariableId id=variable.get_id();
    assert(id<LEN);
    //cout << "weight of" << id << " is " << hash_weights.get(id) << endl;
    valuation[id] = new_value;
  }
  void change_value(const Variable &variable,Value delta){
    set_value(variable,get_value(variable)+delta);
  }
  
  State()
  {
    memset(valuation,0,sizeof(valuation));  
  }
  State(istream &sin)
  {
    uint32 n;
    sin >> n;
    memset(valuation,0,sizeof(valuation));
    assert(n<=LEN);
    for(uint32 i=0;i<n;++i){
      string name;
      sin >> name;
      name_to_id.declare(name);
      Variable variable(name);
      Value value(readValue(sin));
      assert(LEN>variable.get_id());
        
      set_value(variable,value);
    }
  }
  
  friend ostream & operator << (ostream & sout, const State s){
    sout << '[';
    for(uint32 i=0;i<LEN;++i){
      sout << (uint32)s.valuation[i] << ',';
    }
    return sout <<']';
  }
  //innest loop :)
  bool is_dominated_by(const Domination & domination,State big)const{
//    bool escalated = false;
//    ctrace << "does" << endl << (*this) << "dominates" << big << endl;
    for(uint32 i=0;i<LEN;++i){
      Value todo = valuation[i];
      for(uint32 j=i;;){
        
        todo-=big.valuation[j];
        if(todo<=0){
          big.valuation[j]=-todo;
          break;
        }else{
          const int32 up=domination.go_up(j);
          if(up<0){
            return false;
          }
//          escalated=true;
          big.valuation[j]=0;          
          j=up;
        }
      }
    }
//    if(escalated){
//      ctrace << "used escalation for " << (*this) << " vs. " << original << endl;
//    }
    return true;
  }
  size_t hash()const{
    size_t h=0;
    for(uint32 i=0;i<LEN;++i){
      h = h*5+valuation[i];
    }
    return h;
  }
};
namespace __gnu_cxx{
  template<>
  struct hash<pair<State,State> > 
  {
    size_t operator()(const pair<State,State> &arg) const
    {
      return arg.first.hash()+arg.second.hash();
    }
  };
  
  template<>
  struct hash<State> 
  {
    size_t operator()(const State &arg) const
    {
      return arg.hash();
    }
  };
  
}

class ICondition {
public:  
  virtual bool holds(const State &state)=0;
  virtual void output(ostream & sout)=0;
};
class IConditionsParser{
public:
  virtual ICondition * parse(istream & sin)=0;
};
IConditionsParser * conditions_parser;
class AlwaysCondition : public ICondition{
public:  
  virtual bool holds(const State &state){
    return true;
  }
  virtual void output(ostream & sout){
    sout << "true";
  }
};
class LowerBoundCondition : public ICondition{
  Variable variable;
  Value lower_bound;
public:  
  LowerBoundCondition(const Variable &variable,Value lower_bound):variable(variable),lower_bound(lower_bound){
  }
  LowerBoundCondition(istream & sin):variable(sin),lower_bound(readValue(sin)){}
  virtual bool holds(const State &state){
    return lower_bound<=state.get_value(variable);
  }
  virtual void output(ostream & sout){
    
    sout << variable << ">=" << (uint32)lower_bound;
  }
};
class ConjunctionCondition : public ICondition{
  ICondition * a;
  ICondition * b;
public:  
  ConjunctionCondition(ICondition * a,ICondition * b):a(a),b(b){}
  ConjunctionCondition(istream & sin){
    a = conditions_parser->parse(sin);
    b = conditions_parser->parse(sin);
  }
  virtual bool holds(const State &state){
    return a->holds(state) && b->holds(state);
  }
  virtual void output(ostream & sout){
    sout << "(";
    a->output(sout);
    sout << ")&&(";
    b->output(sout);
    sout << ")";
  }
};
class ConditionsParser : public IConditionsParser{
public:
  virtual ICondition * parse(istream & sin){
    string name;
    sin >> name;
    if(">=" == name){
      return new LowerBoundCondition(sin);
    }else if("&&" == name){
      return new ConjunctionCondition(sin);
    }else{
      cerr << "Unknown condition: " << name << endl;
      throw "Unknown condition";
    }
  }
};

class IAction{
public:  
  virtual ICondition * get_condition()const=0;
  virtual void reserve(State &state)const=0;
  virtual void release(State &state)const=0;
  
  virtual void execute(State &state)const=0;
  virtual void rollback(State &state)const=0;
  
  virtual void output(ostream & sout)const=0;
  virtual bool obligatory()const=0;//optimization
};
class IActionsParser{
public:
  virtual IAction * parse(istream & sin)=0;
};
IActionsParser * actions_parser;

class ConditionalAction : public IAction{
  ICondition * condition;
public:  
  ConditionalAction(ICondition * condition):condition(condition){}
  virtual ICondition * get_condition()const{
    return condition;
  }
  virtual void output(ostream & sout)const{
  }
  virtual bool obligatory()const{
    return false;
  }
};

class ChangeAction : public ConditionalAction{
protected:
  Variable variable;
  Value delta;
public:
  ChangeAction(ICondition * condition,const Variable &variable,Value delta):ConditionalAction(condition),variable(variable),delta(delta){}
  virtual void reserve(State &state)const{
    state.change_value(variable,delta);
  }
  virtual void release(State &state)const{
    state.change_value(variable,-delta);
  }
  virtual void execute(State &state)const{
    state.change_value(variable,delta);
  }
  virtual void rollback(State &state)const{
    state.change_value(variable,-delta);
  }
};
class EarnAction : public ChangeAction{
public:
  EarnAction(const Variable &variable,Value change):ChangeAction(new AlwaysCondition(),variable,+change){}
  virtual void reserve(State &state)const{
  }
  virtual void release(State &state)const{
  }
};
class SpendAction : public ChangeAction{
public:
  SpendAction(const Variable &variable,Value change):ChangeAction(new LowerBoundCondition(variable,change),variable,-change){}
};
class NamedAction : public IAction{
  string name;
  IAction * a;
public:
  NamedAction(string name,IAction * a):name(name),a(a){}
  virtual void output(ostream & sout)const{
    sout << name;
  }
  virtual ICondition *  get_condition()const{
    return a->get_condition();
  }
  virtual void reserve(State &state)const{
    a->reserve(state);
  }
  virtual void release(State &state)const{
    a->release(state);
  }
  virtual void execute(State &state)const{
    a->execute(state);
  }
  virtual void rollback(State &state)const{
    a->rollback(state);
  }
  virtual bool obligatory()const{
    return a->obligatory();
  }
  virtual ~NamedAction(){
    assert(false);
    delete a;
  }
};


class CompoundAction : public ConditionalAction{
protected:
  IAction *a;
  IAction *b;
public:
  CompoundAction(IAction *a,IAction *b):ConditionalAction(new ConjunctionCondition(a->get_condition(),b->get_condition())),a(a),b(b){}
  virtual void reserve(State &state)const{
    a->reserve(state);
    b->reserve(state);
  }
  virtual void release(State &state)const{
    a->release(state);
    b->release(state);
  }
  virtual void execute(State &state)const{
    a->execute(state);
    b->execute(state);
  }
  virtual void rollback(State &state)const{
    b->rollback(state);
    a->rollback(state);
  }
};

class ObligatoryAction : public IAction{
  IAction *a;
public:  
  ObligatoryAction(IAction *a):a(a){}
  virtual void reserve(State &state)const{
    a->reserve(state);
  }
  virtual void release(State &state)const{
    a->release(state);
  }
  virtual void execute(State &state)const{
    a->execute(state);
  }
  virtual void rollback(State &state)const{
    a->rollback(state);
  }
  virtual bool obligatory()const{
    return true;
  }
  virtual void output(ostream & sout)const{
    a->output(sout);
  }
  virtual ICondition * get_condition()const{
    return a->get_condition();
  }
};

class ParsableCompoundAction : public CompoundAction{
public:
  ParsableCompoundAction(istream & sin):CompoundAction(actions_parser->parse(sin),actions_parser->parse(sin)){}
};

class ConditionedAction : public ConditionalAction{
  IAction *a;
public:  
  ConditionedAction(IAction *a,ICondition * c):ConditionalAction(new ConjunctionCondition(c,a->get_condition())),a(a){}
  virtual void reserve(State &state)const{
    a->reserve(state);
  }
  virtual void release(State &state)const{
    a->release(state);
  }
  virtual void execute(State &state)const{
    a->execute(state);
  }
  virtual void rollback(State &state)const{
    a->rollback(state);
  }
};
class ParsableConditionedAction : public ConditionedAction{
public:
  ParsableConditionedAction(istream & sin):ConditionedAction(actions_parser->parse(sin),conditions_parser->parse(sin)){}
};


class ActionsParser : public IActionsParser{
private:
  template<typename T>
  IAction * parse_change(istream & sin){
    Variable variable(sin);
    Value change(readValue(sin));
    return new T(variable,change);
  }
public:
  virtual IAction * parse(istream & sin){
    string name;
    sin >> name;
    if("earn"==name){
      return parse_change<EarnAction>(sin);
    }else if("spend"==name){
      return parse_change<SpendAction>(sin);
    }else if("compound"==name){
      return new ParsableCompoundAction(sin);
    }else if("conditioned"==name){
      return new ParsableConditionedAction(sin);
    }else if("named"==name){
      string action_name;
      sin >> action_name;
      return new NamedAction(action_name,parse(sin));
    }else if("obligatory"==name){
      return new ObligatoryAction(parse(sin));
    }else{
      throw "Unknown action";
    }
  }
};

class Actions : public vector<IAction *>{
public: 
  Actions(istream & sin){
    uint32 m;
    sin >> m;
    ActionsParser parser;
    for(uint32 i=0;i<m;++i){
      push_back(parser.parse(sin));
    }
  }
};
class States : public slist<State>{
};
typedef slist<const IAction*> Orders;

#ifdef HASH_MAP_HISTORY
class History : private hash_map<State,Orders>{
public:
  bool contains(const State &state)const{
    return hash_map<State,Orders>::find(state)!=hash_map<State,Orders>::end();    
  }
  void insert(pair<State,Orders> pair){
    hash_map<State,Orders>::insert(pair);
  }
  Orders get_orders(const State &state)const{
    return find(state)->second;
  }
  size_t size()const{
    return hash_map<State,Orders>::size();
  }
  hash_map<State,Orders>::iterator begin(){
    return hash_map<State,Orders>::begin();
  }
  hash_map<State,Orders>::iterator end(){
    return hash_map<State,Orders>::end();
  }
};
#else
class History : private slist<pair<const State,Orders> >{
private:
  typedef slist<pair<const State,Orders> > base;
  typedef base::iterator iterator;
  static const uint32 BUCKETS_COUNT=1<<16;
  iterator bucket[BUCKETS_COUNT];
  uint32 n;
public:
  History():n(0){
    for(uint32 i=0;i<BUCKETS_COUNT;++i){
      bucket[i] = base::end();
    }
  }
  bool contains(const State &state)const{
//    ctrace << "contains" << endl;
    const uint32 h=state.hash()%BUCKETS_COUNT;
    for(iterator it=bucket[h];it!=base::end();++it){
      if(it->first==state){
        return true;
      }else if(it->first.hash()%BUCKETS_COUNT!=h){
        return false;
      }
    }
    return false;    
  }
  void insert(pair<State,Orders> p){
//    ctrace << "insert" << endl;
    ++n;
    const uint32 h=p.first.hash()%BUCKETS_COUNT;
    if(bucket[h]==base::end()){
      base::push_front(p);
      bucket[h]=base::begin();
    }else{
      base::insert_after(bucket[h],p);
    }
  }
  Orders get_orders(const State &state)const{
//    ctrace << "get_orders" << endl;
    const uint32 h=state.hash()%BUCKETS_COUNT;
    for(iterator it=bucket[h];it!=base::end();++it){
      if(it->first==state){
        return it->second;
      }else if(it->first.hash()%BUCKETS_COUNT!=h){
        assert(false);
      }
    }
    assert(false);
  }
  size_t size()const{
    return n;
  }
  base::iterator begin(){
    return base::begin();
  }
  base::iterator end(){
    return base::end();
  }  
};
#endif
class IProcessor{
public:
  virtual States make_step(const Domination &domination,const Time time,const Actions & actions,States states,History & history)=0;
};
//uwaga! 
//  stan to nie tylko wartoœci zmiennych,
//  to tak¿e zbiór akcji jakie jeszcze rozwa¿amy wykonaæ
//  dlatego powinniœmy najpierw daæ szansê dojœæ do danego stanu bez przesuwania begin
//  tak aby w razie remisu, pierwszeñstwo mia³ ten stan w którym wci¹¿ mo¿emy wykonaæ jakieœ akcje
//wiêc:
//  pomys³ z recursively, by³ bardzo z³y (odpowiada³ czemuœ na kszta³t DFS zamiast BFS)
//uwaga!
//  stan to te¿ zakomitowane resourcey -- jeœli do tego samego stanu umiem dojœæ komituj¹c mniej
//  to przecie¿ znacznie lepsza sytuacja!
typedef pair<State,State> StatePair;
class IterativeProcessor : public IProcessor{
   //          executed , reserved
  typedef hash_map<StatePair,const IAction*>  RecentHistory;
  typedef vector<StatePair> StatePairs;
  static bool a_dominates_b_on_both(const Domination &domination,const StatePair &a,const StatePair &b){
    return b.first.is_dominated_by(domination,a.first)&&b.second.is_dominated_by(domination,a.second);
  }
  static bool a_dominates_b_on_first(const Domination &domination,const StatePair &a,const StatePair &b){
    return b.first.is_dominated_by(domination,a.first);
  }
  
  void maximums(
    bool a_dominates_b(const Domination &domination,const StatePair &a,const StatePair &b),
    const Domination &domination,
    StatePairs &new_state_pairs,
    uint32 MAX_ATTEMPTS=1000
  )const{
    sort(new_state_pairs.begin(),new_state_pairs.end());
    reverse(new_state_pairs.begin(),new_state_pairs.end());//greater?
    uint32 last=0;
    for(uint32 i=0;i<new_state_pairs.size();++i){
      assert(i+1>=new_state_pairs.size() || new_state_pairs[i]!=new_state_pairs[i+1]);
      bool dominated = false;
      for(uint32 j=last;j-->last-min(last,MAX_ATTEMPTS);){
        if(a_dominates_b(domination,new_state_pairs[j],new_state_pairs[i])){
          dominated = true;
          //ctrace << "dominated by " << j << ' ' << last-j << endl;
          break;
        }
      }
      if(dominated){
        
      }else{
        //ctrace << "not dominated" << endl;
        swap(new_state_pairs[last++],new_state_pairs[i]);
      }
    }
    new_state_pairs.resize(last);
    //ctrace << "domino:" << new_state_pairs.size() << " to " << last << endl;
  }
  void copy_history_of(const RecentHistory & source_history,RecentHistory & destination_history,const StatePairs &state_pairs)const{
    ctrace.enter();
    foreach(state_pairs,state_pair){
      for(StatePair current_pair=*state_pair;current_pair.first!=current_pair.second;){
        if(destination_history.find(current_pair)!=destination_history.end()){
          break;
        }
        pair<StatePair,const IAction*> howto=undo(current_pair,source_history);
        destination_history[current_pair]=howto.second;
        current_pair=howto.first;
      }
    }
    ctrace.leave();
  }
  void cleanup_recent_history(RecentHistory & recent_history,const StatePairs &state_pairs)const{
    ctrace.enter();
    RecentHistory clean_history;
    copy_history_of(recent_history,clean_history,state_pairs);
    swap(recent_history,clean_history);
    ctrace.leave();
  }
  pair<StatePair,const IAction*> undo(StatePair state_pair,const RecentHistory & recent_history)const{
    RecentHistory::const_iterator it=recent_history.find(state_pair);
    assert(it!=recent_history.end());
    const IAction * action = it->second;
    assert(NULL!=action);
    action->release(state_pair.second);
    action->rollback(state_pair.first);
    return make_pair(state_pair,action);
  }
  void verify_recent_history_conistency(const RecentHistory & recent_history,const StatePairs & state_pairs)const{
    ctrace.enter();
    foreach(state_pairs,state_pair){
      Orders orders;
      backtrack_orders(*state_pair,recent_history,orders);
    }
    ctrace.leave();
  }
  void occasional_purging(const Domination & domination,RecentHistory & recent_history, StatePairs & new_state_pairs,const StatePairs::iterator begin,const StatePairs::iterator end)const{
    ctrace.enter();
    
    maximums(a_dominates_b_on_both,domination,new_state_pairs);
    StatePairs old_state_pairs(begin,end);
    
    {
      RecentHistory new_history;
    
      copy_history_of(recent_history,new_history, new_state_pairs );
    
      copy_history_of(recent_history,new_history, old_state_pairs );
    
      swap(new_history,recent_history);
    }
    ctrace << "verifying old after purging" << endl;
    verify_recent_history_conistency(recent_history,old_state_pairs);
    ctrace << "verifying new after purging" << endl;
    verify_recent_history_conistency(recent_history,new_state_pairs);
    ctrace.leave();
  }
  void post_action_purging(const Domination & domination,RecentHistory & recent_history,StatePairs & new_state_pairs)const{
    ctrace.enter();
    maximums(a_dominates_b_on_both,domination,new_state_pairs);
    cleanup_recent_history(recent_history,new_state_pairs);
    ctrace << "verifying after action purging" << endl;
    verify_recent_history_conistency(recent_history,new_state_pairs);
    ctrace.leave();
  }
  void final_purging(const Domination & domination,RecentHistory & recent_history, StatePairs & state_pairs)const{
    ctrace.enter();
    maximums(a_dominates_b_on_first,domination,state_pairs);//,state_pairs.size());
    ctrace << "cleaning up" << endl;
    cleanup_recent_history(recent_history,state_pairs);
    ctrace << "verifying after final purging" << endl;
    verify_recent_history_conistency(recent_history,state_pairs);
    ctrace.leave();
  }
  void by_history_purging(const History &history,RecentHistory & recent_history,StatePairs & state_pairs){
    ctrace.enter();
    uint32 write_offset=0;
    for(uint32 i=0;i<state_pairs.size();++i){
      if(!history.contains(state_pairs[i].first)){
        state_pairs[write_offset++]=state_pairs[i];
      }
    }
    state_pairs.resize(write_offset);
    cleanup_recent_history(recent_history,state_pairs);
    ctrace << "verifying after history purging" << endl;
    verify_recent_history_conistency(recent_history,state_pairs);
    ctrace.leave();
  }
  typedef pair<StatePairs,RecentHistory> LeavesAndTree;
  LeavesAndTree make_step(const Domination & domination,const Actions & actions,const States states,const History & history){
    ctrace.enter();
    LeavesAndTree leaves_and_tree;
    StatePairs &state_pairs=leaves_and_tree.first;
    RecentHistory &recent_history=leaves_and_tree.second;
    
    state_pairs.reserve(states.size());
    foreach(states,state){
      state_pairs.push_back(StatePair(*state,*state));
    }
    //w tym momencie, mamy same pary (x,x), zaœ akcje (wysokopoziomowe) execute!=reserve
    //wiêc dla ¿adnej akcji A i par (x,x) i (y,y), ani ¿adnego wyk³adnika i = 0,1,...
    //nie mo¿e byæ A^i(x,x)=(y,y)
    //co wiêcej: A jest ró¿nowartoœciowa, wiec 
    //  A^i(x,x) != A^i(y,y)
    //a co ciekawsze: 
    //  A^i(x,x) == A^j(y,y) dla i>j implikowa³oby A^(i-j)(x,x) = (y,y)
    //wiêc ostatecznie mamy:
    //  A^i(x,x) != A^j(y,y) dla dowolnych x!=y, i,j >=0
    uint32 action_no = 1;
    ctrace << "looping through " << actions.size() << " actions" << endl;
    foreach(actions,action_it){
      ctrace << "action #" << action_no << endl;
      ctrace.enter();
      const IAction * action = *action_it;
      StatePairs new_state_pairs;//= state_pairs;
      size_t gc_threshold = 100000;
      new_state_pairs.reserve(200000);
      foreach(state_pairs,state_pair_it){
        ctrace.enter();
        //dla ka¿dego (x,y) tworzone s¹ A(x,y), A(A(x,y)),...
        //przy za³o¿eniu indukcyjnym, ¿e:
        //  A^i(x',y')!=A^j(x,y)  [tak¿e dla i=0, czy j=0]
        State gained_state = state_pair_it->first;
        State paid_state = state_pair_it->second;
        bool add=true;
        while(action->get_condition()->holds(paid_state)){
          if(!action->obligatory()){
            new_state_pairs.push_back(StatePair(gained_state,paid_state));
          }
          action->reserve(paid_state);
          action->execute(gained_state);
          if(history.contains(gained_state)){
            add=false;
            break;//is it correct?
          }
          const StatePair new_state_pair(gained_state,paid_state);
          assert(recent_history.insert(make_pair(new_state_pair,action)).second);
        }
        if(add){
          const StatePair new_state_pair(gained_state,paid_state);
          new_state_pairs.push_back(new_state_pair);
        }
        //no i teraz dlaczego mamy zapewniony krok indukcyjny?
        //niech A* bêdzie operacj¹ na zbiorach par, tak¹, ¿e:
        // A*(S) = { A^i(x,y) | (x,y) in S, i = 0,1,...}
        //niech S bêdzie zwany A-odpornym, gdy A^i(x,y) != A^j(x',y') dla (x,y)!=(x',y') i ka¿dych i,j
        //niech S bêdzi A-odporny
        //chcê pokazaæ, ¿e A*(S) jest B-odporny, dla ka¿dej akcji B.
        //Za³ó¿my przeciwnie, ¿e B^iA^k(x,y) = B^jA^l(x',y') dla pewnych (x,y),(x',y') in S oraz i>=j  
        // B jest ró¿nowartoœciowa, wiêc:
        // B^(i-j)A^k(x,y) = A^l(x',y')
        //sk³adanie akcji (o ile s¹ dopuszczalne) jest przemienne (bo to s¹ przesuniêcia)
        // A^kB^(i-j)(x,y) = A^l(x',y')
        //mamy wiêc dwa przypadki:
        //1. k>=l
        //  A^(k-l)B^(i-j)(x,y) = (x',y') 
        if(new_state_pairs.size()>=gc_threshold){
          ctrace << action_no << " purging above "<<gc_threshold<<endl;
          occasional_purging( domination,recent_history,new_state_pairs,state_pair_it+1,state_pairs.end());
          gc_threshold=new_state_pairs.size()*2;
        }
        ctrace.leave();
      }
      ctrace << "purging" << endl;
      post_action_purging(domination,recent_history,new_state_pairs);
          //const uint32 original_number_of_pairs=new_state_pairs.size();
      //,new_state_pairs.size());
      swap(state_pairs,new_state_pairs);
//      clog << "purged: " << state_pairs.size() << ' ' << original_number_of_pairs << "       \n";
      action_no++;
      ctrace.leave();
    }
    domination_and_history_purging(domination,history,leaves_and_tree);
    ctrace.leave();
    return leaves_and_tree;
  }
  void domination_and_history_purging(const Domination & domination,const History & history,LeavesAndTree &leaves_and_tree){
    ctrace.enter();
    StatePairs &state_pairs=leaves_and_tree.first;
    RecentHistory &recent_history=leaves_and_tree.second;
    ctrace << "final purging from " << state_pairs.size() << endl;
    final_purging(domination,recent_history,state_pairs);
    ctrace << state_pairs.size() << " dominating candidates left" << endl;
    ctrace << "by history puring" << endl;
    by_history_purging(history,recent_history,state_pairs);
    ctrace << "prepared to add:" << state_pairs.size() << endl;
    ctrace.leave();
  }
  void merge_results(LeavesAndTree &a,const LeavesAndTree &b)const{
    ctrace.enter();
    foreach(b.first,state_pair){
      if(state_pair->first==state_pair->second || a.second.find(*state_pair)==a.second.end()){
        a.first.push_back(*state_pair);
        for(StatePair pair=*state_pair;pair.first!=pair.second;){
          if(a.second.find(pair)!=a.second.end()){
            break;
          }
          a.second.insert(*b.second.find(pair));
          pair=undo(pair,b.second).first;
        }
      }
    }
    ctrace.leave();
  }
public:
  virtual States make_step(const Domination & domination, const Time time,const Actions & actions,const States states,History & history){
    ctrace.enter();
    
    LeavesAndTree leaves_and_tree;
    
    const uint32 parts=10;
    for(uint32 part=0;part<parts;++part){
      const uint32 part_start=states.size()*part/parts;
      const uint32 part_end=states.size()*(part+1)/parts;
      if(part_start<part_end){
        ctrace << "part #" << part << " of " << parts << endl;
        States states_part;
        States::const_iterator it=states.begin();
        for(uint32 i=0;i<part_end;++i){
          if(part_start<=i){
            states_part.push_front(*it);
          }
          ++it;
        }
        {
          ctrace << "making step" << endl;
          LeavesAndTree leaves_and_tree2=make_step(domination,actions,states_part,history);
          ctrace << "merging" << endl;
          merge_results(leaves_and_tree,leaves_and_tree2);
        }
        ctrace << "purging after merge" << endl;
        final_purging(domination,leaves_and_tree.second,leaves_and_tree.first);
      }
    }
    
    
    StatePairs &state_pairs=leaves_and_tree.first;
    RecentHistory &recent_history=leaves_and_tree.second;
    
    States new_states;
    foreach(state_pairs,state_pair_it){
      const State gained_state = state_pair_it->first;
      assert(!history.contains(gained_state));
      Orders orders;
      backtrack_orders(*state_pair_it,recent_history,orders);
      history.insert(make_pair(gained_state,orders));
      new_states.push_front(gained_state);
    }
    ctrace.leave(); 
    return new_states;
  }
  void backtrack_orders(const StatePair & state_pair,const RecentHistory & recent_history,Orders & orders)const{
    if(recent_history.find(state_pair)==recent_history.end()){
      if(state_pair.first != state_pair.second){
        cerr << "state: " << state_pair.first << "x" << state_pair.second << " is missing!" << endl;
        assert(state_pair.first == state_pair.second);
      }
    }else{
      pair<StatePair,const IAction*> previous_and_action = undo(state_pair,recent_history);
      backtrack_orders(previous_and_action.first,recent_history,orders);
      orders.push_front(previous_and_action.second);
    }
  }
};
void backtrack(const State & init_state,const History & history,const State &state){
  ctrace.enter();
  cout << "backtracking:" << state << endl;
  if(init_state!=state){
    State previous=state;
    const Orders real_orders=history.get_orders(state);
    vector<const IAction *> orders(real_orders.begin(),real_orders.end());
    foreach(orders,order){
      (*order)->rollback(previous);
    }
    backtrack(init_state,history,previous);
    cout << "perform:";
    for(uint32 i=orders.size();i--;){
      cout <<' ';
      orders[i]->output(cout);
      assert(orders[i]->get_condition()->holds(previous));
      orders[i]->execute(previous);
    }
    cout << endl;
    assert(previous == state);
    //ctrace << "to get to state " << state << endl;
  }else{
    ctrace << "starting from" << state << endl;
  }
  ctrace.leave();
}

typedef set<State> StatesSet;
void reach(const State &state,History & history,StatesSet &reachable){
  if(reachable.insert(state).second){
    State previous = state;
    const Orders orders=history.get_orders(state);
    foreach(orders,order){
      (*order)->rollback(previous);
    }
    reach(previous,history,reachable);
  }
}
typedef ICondition * Mission;
class Missions : public vector<Mission>{
public:
  Missions(){
  }
  Missions(istream & sin){
    uint32 n;
    sin >> n;
    reserve(n);
    for(uint32 i=0;i<n;++i){
      Mission mission = conditions_parser->parse(sin);
      push_back(mission);
    }
  }
};
States::const_iterator find_misson_resolution(const Mission mission,const States & states){
  States::const_iterator found=states.end();
  foreach(states,state){
    if(mission->holds(*state)){
      found = state;
    }
  }
  return found;
}
void resolve_missions(Missions & missions,const States & states,const State &init_state,const History & history){
  Missions uncompleted_missions;
  foreach(missions,mission){
    States::const_iterator resolution=find_misson_resolution(*mission,states);
    if(resolution==states.end()){
      uncompleted_missions.push_back(*mission);
    }else{
      
      cout << "mission ";
      (*mission)->output(cout);
      cout << " accomplished" << endl;
      backtrack(init_state,history,*resolution);
      
    }
  }
  swap(missions,uncompleted_missions); 
}
int main(){
  clock_t start=clock();
  conditions_parser = new ConditionsParser();
  actions_parser = new ActionsParser();
  IProcessor * processor = new IterativeProcessor();
  State init_state(cin);
  History history;
  history.insert(make_pair(init_state,Orders()));//¿eby nie by³o pêtli
  Actions actions(cin);
  Domination domination(cin);
  Missions missions(cin);
  
  States states;
  states.push_front(init_state);



  for(Time t=0;t<100;++t){
    ctrace.enter();
    
    resolve_missions(missions,states,init_state,history);
    if(missions.empty()){
      clock_t end=clock();
      cout << "all missions accomplished in t=" << t << endl;
      ctrace << "done in " << end-start << endl;
      return 0;
    }
    
    states=processor->make_step(domination,t,actions,states,history);
    
    ctrace << "checking reachability" << endl;
    StatesSet reachable;
    foreach(states,state){
      reach(*state,history,reachable);
    }
    const uint32 states_size = states.size();
    const uint32 history_size = history.size();
    const uint32 reachable_size = reachable.size();
    
    ctrace << "garbage_collecting" << endl;
    uint32 collected=0;
    uint32 uncollected=0;
    
    foreach(history,history_it){
      if(!history_it->second.empty() && reachable.find(history_it->first)==reachable.end()){
        collected+=history_it->second.size();
        Orders empty_orders;
        swap(history_it->second,empty_orders);
      }else{
        uncollected+=history_it->second.size();
      }
    }
    reachable.clear();
    ctrace << "time=" << t << " (" << (clock()-start)  << ") "<< states_size << " " << history_size << " " << reachable_size <<" " << collected << " " << uncollected << "      " << endl;
    if(states_size < 30){
      foreach(states,state){
        cout << *state << endl;
      }
    }
    cout << "time=" << t << ' ';
    slabocator.show_stats(cout);
    ctrace.leave();
  }
  return 0;
}
