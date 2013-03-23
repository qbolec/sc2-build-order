#include<iostream>
#include<string>
#include<vector>
using namespace std;
#define foreach(c,it) for(typeof((c).begin()) it=(c).begin();it!=(c).end();++it)
typedef unsigned int uint32;
void expect(string what){
  string got;
  cin >> got;
  if(got!=what){
    cerr << "expected " << what << " got: " << got << endl;
    assert(got==what);
  }
}
typedef pair<string,uint32> KeyVal;
typedef vector<KeyVal> Valuation;
Valuation read_valuation(){
  uint32 fixed_vars;
  cin >> fixed_vars;
  Valuation initial_state;
  for(uint32 i=0;i<fixed_vars;++i){
    string name;
    uint32 value;
    cin >> name >> value;
    initial_state.push_back(make_pair(name,value));
  }
  return initial_state;
}
void write_valuation(Valuation valuation){
  cout << valuation.size() << endl;
  foreach(valuation,p){
    cout << p->first << ' ' << p->second << endl;
  }

}
struct SCRule{
  string name;
  string starting_state;
  uint32 time;
  uint32 parallelizm;
  Valuation earnings;
  Valuation spendings;
};
string working_state(string name,uint32 step){
  char name_buffer[256];
  sprintf(name_buffer,"%s-working-%u",name.c_str(),step);
  return string(name_buffer);
}
string progress_state(string name,uint32 step){
  char name_buffer[256];
  sprintf(name_buffer,"%s-progress-%u",name.c_str(),step);
  return string(name_buffer);
}
string site_lock(string rule_name,uint32 site_id){
  char buffer[256];
  sprintf(buffer,"%s-lock-%d",rule_name.c_str(),site_id);
  return buffer;
}
void declare_state_variables(Valuation & initial_state,SCRule rule){
  if(0==rule.parallelizm){
    assert(rule.time>=2);
    for(uint32 i=rule.time-1;i--;){
      initial_state.push_back(make_pair(working_state(rule.name,i),0));
    }
  }else{
    for(uint32 i=0;i<rule.parallelizm;++i){
      initial_state.push_back(make_pair(site_lock(rule.name,i),1));
    }
    for(uint32 i=rule.parallelizm;i--;){
      initial_state.push_back(make_pair(working_state(rule.name,i),0));
      initial_state.push_back(make_pair(progress_state(rule.name,i),0));
    }
  }
}
struct GameRule{
  bool named;
  bool obligatory;
  string name;
  Valuation spendings;
  Valuation earnings;
  GameRule(string name):named(true),obligatory(false),name(name){}
  GameRule(bool obligatory):named(false),obligatory(obligatory){}
};
typedef vector<GameRule> GameRules;
void add_game_rules(GameRules & game_rules,SCRule rule){
  if(0==rule.parallelizm){
    GameRule begin(rule.name);
    begin.spendings=rule.spendings;
    begin.spendings.push_back(make_pair(rule.starting_state,1));
    begin.earnings.push_back(make_pair(working_state(rule.name,0),1));
    game_rules.push_back(begin);
    
    for(uint32 i=1;i<rule.time-1;++i){
      GameRule transition(true);
      transition.spendings.push_back(make_pair(working_state(rule.name,i-1),1));
      transition.earnings.push_back(make_pair(working_state(rule.name,i),1));
      game_rules.push_back(transition);
    }
    
    GameRule end(true);
    assert(0<rule.time);
    end.spendings.push_back(make_pair(working_state(rule.name,rule.time-2),1));
    end.earnings=rule.earnings;
    end.earnings.push_back(make_pair(rule.starting_state,1));
    game_rules.push_back(end);
  }else{
    assert(2<=rule.time);
    // step = 128/time . chodzi o to, by nie op³aca³o siê (dziêki overflow) kontynuowaæ budowy po jej zakoñczeniu
    const uint32 step=128/(rule.time-1);
    // for site_id = 1..parallelizm
    for(uint32 site_id=0;site_id<rule.parallelizm;++site_id){
    //   spendings + starting_state + site_lock[site_id] = working_state[site_id] + step*progress_state[site_id]
      char buffer[256];
      sprintf(buffer,"%s-at-site-%d",rule.name.c_str(),site_id);
      GameRule begin((string)buffer);
      begin.spendings = rule.spendings;
      begin.spendings.push_back(make_pair(rule.starting_state,1));
      begin.spendings.push_back(make_pair(site_lock(rule.name,site_id),1));
      begin.earnings.push_back(make_pair(working_state(rule.name,site_id),1));
      begin.earnings.push_back(make_pair(progress_state(rule.name,site_id),step));
      game_rules.push_back(begin);
    //   ((time-1)*step)*progress_state[site_id] + working_state[site_id] = earnings + starting_state + site_lock[site_id]
      GameRule end(true);
      end.spendings.push_back(make_pair(progress_state(rule.name,site_id),(rule.time-1)*step));
      end.spendings.push_back(make_pair(working_state(rule.name,site_id),1));
      end.earnings = rule.earnings;
      end.earnings.push_back(make_pair(rule.starting_state,1));
      end.earnings.push_back(make_pair(site_lock(rule.name,site_id),1));
      game_rules.push_back(end);
    // kolejnoœæ akcji obligatory w pliku wyjœciowym ma znaczenie
    // dlatego najpierw doda³em regu³ê koñcow¹, a dopiero teraz tê œrodkow¹
    // tak aby scv móg³ skoñczyæ budowê, zamiast dalej j¹ ci¹gn¹æ
    //   working_state[site_id] = working_state[site_id] + step*progress_state[site_id]
      if(1<rule.time){
        GameRule progression(true);
        progression.spendings.push_back(make_pair(working_state(rule.name,site_id),1));
        progression.earnings = progression.spendings;
        progression.earnings.push_back(make_pair(progress_state(rule.name,site_id),step));
        game_rules.push_back(progression);
      }
    
    
    }
  }
}
void write_rules(GameRules game_rules){
  cout << game_rules.size() << endl;
  foreach(game_rules,game_rule){
    if(game_rule->named){
      cout << "named " << game_rule->name << endl;
    }
    if(game_rule->obligatory){
      cout << "obligatory" << endl;
    }
    foreach(game_rule->spendings,spend){
      if(spend+1!=game_rule->spendings.end()||!game_rule->earnings.empty()){
        cout << "compound ";
      }
      cout << "spend " << spend->first << ' ' << spend->second << endl;
    }
    foreach(game_rule->earnings,earn){
      if(earn+1!=game_rule->earnings.end()){
        cout << "compound ";
      }
      cout << "earn " << earn->first << ' ' << earn->second << endl;
    }
    cout << endl;
  }
}
typedef pair<string,string> Inequality;
typedef vector<Inequality> Inequalities;
void add_inequalities(Inequalities & inequalities,SCRule rule){
  if(0==rule.parallelizm){
    for(uint32 i=1;i<rule.time-1;++i){
      inequalities.push_back(Inequality(working_state(rule.name,i-1),working_state(rule.name,i)));
    }
  }else{
    //lepiej rozgrzebywaæ wy¿sze sitey
    for(uint32 site_id=1;site_id<rule.parallelizm;++site_id){
      inequalities.push_back(Inequality(working_state(rule.name,site_id-1),working_state(rule.name,site_id)));
      inequalities.push_back(Inequality(progress_state(rule.name,site_id-1),progress_state(rule.name,site_id)));
      //a tutaj na odwrót:
      inequalities.push_back(Inequality(site_lock(rule.name,site_id),site_lock(rule.name,site_id-1)));
    }
  }
}
void write_inequalities(Inequalities inequalities){
  cout << inequalities.size() << endl;
  foreach(inequalities,inequality){
    cout << inequality->first << ' ' <<inequality->second << endl;
  }
}
int main(){
  
  Valuation initial_state=read_valuation();
  
  uint32 rules_count;
  cin >> rules_count;
  vector<SCRule> rules;
  for(uint32 i=0;i<rules_count;++i){
    SCRule rule;
    cin >> rule.name;
    expect("starts-in");
    cin >> rule.starting_state;
    expect("parallelizm");
    cin >> rule.parallelizm;
    expect("time");
    cin >> rule.time;
    assert(rule.time>=2);
    expect("spend");
    rule.spendings =read_valuation();
    expect("earn");
    rule.earnings =read_valuation();
    clog << rule.name << endl;
    declare_state_variables(initial_state,rule);
    rules.push_back(rule);
  }
  write_valuation(initial_state);
  GameRules game_rules;
  foreach(rules,rule){
    add_game_rules(game_rules,*rule);
  }
  write_rules(game_rules);
  Inequalities inequalities;
  foreach(rules,rule){
    add_inequalities(inequalities,*rule);
  }
  write_inequalities(inequalities);
  return 0;
}
