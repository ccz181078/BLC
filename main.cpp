#include<bits/stdc++.h>
struct Node;
typedef std::shared_ptr<Node> pNode;
uint64_t node_cnt=0;
uint64_t MAX_NODE_NUM=1e4;

struct Node{
    int id;
    pNode ch[2];
    Node(int id):id(id){++node_cnt;}
    Node(int id,const pNode &x):id(id),ch({x,nullptr}){++node_cnt;}
    Node(int id,const pNode &x,const pNode &y):id(id),ch({x,y}){++node_cnt;}
    ~Node(){--node_cnt;}
};
pNode lam(pNode x){
    return std::make_shared<Node>(-1,x);
}
pNode app(pNode f,pNode x){
    return std::make_shared<Node>(0,f,x);
}
pNode var(int id){
    assert(id>0);
    return std::make_shared<Node>(id);
}

pNode lift(pNode x,int n,int depth=0){
    if(x->id==-1)return lam(lift(x->ch[0],n,depth+1));
    if(x->id==0)return app(lift(x->ch[0],n,depth),lift(x->ch[1],n,depth));
    if(x->id>0)return var(x->id>depth?x->id+n:x->id);
    assert(0);
}

pNode subst(pNode f,pNode x,int depth=1){
    if(f->id==-1){
        return lam(subst(f->ch[0],x,depth+1));
    }
    if(f->id==0){
        return app(subst(f->ch[0],x,depth),subst(f->ch[1],x,depth));
    }
    if(f->id>0){
        if(f->id>depth)return var(f->id-1);
        if(f->id==depth)return lift(x,depth-1);
        return var(f->id);
    }
    assert(0);
}
bool eq_ignore_FV(pNode x,pNode y,int depth=0){
    if(x->id==-1){
        return y->id==-1&&eq_ignore_FV(x->ch[0],y->ch[0],depth+1);
    }
    if(x->id==0){
        return y->id==0&&eq_ignore_FV(x->ch[0],y->ch[0],depth)&&eq_ignore_FV(x->ch[1],y->ch[1],depth);
    }
    if(x->id>0){
        return y->id>0&&(x->id==y->id||(x->id>depth&&y->id>depth));
    }
    assert(0);
}

struct ReduceCtx{
    bool reduce_dup;
    pNode redex;
    ReduceCtx(bool reduce_dup=false):reduce_dup(reduce_dup),redex(nullptr){}
    pNode reduce(pNode x){
        if(node_cnt>=MAX_NODE_NUM)throw int(0);
        if(redex&&!reduce_dup)return x;
        if(x->id==-1)return lam(reduce(x->ch[0]));
        if(x->id==0){
            if(x->ch[0]->id==-1){
                if(redex&&!eq_ignore_FV(redex,x))return x;
                redex=x;
                return subst(x->ch[0]->ch[0],x->ch[1]);
            }
            auto x0=reduce(x->ch[0]);
            auto x1=reduce(x->ch[1]);
            return app(x0,x1);
        }
        if(x->id>0)return var(x->id);
        assert(0);
    }
};
bool no_occur(pNode x,int depth){
    if(x->id==-1){
        return no_occur(x->ch[0],depth+1);
    }
    if(x->id==0){
        return no_occur(x->ch[0],depth)&&no_occur(x->ch[1],depth);
    }
    if(x->id>0){
        return x->id!=depth;
    }
    assert(0);
}
bool eq(pNode x,pNode y){
    if(!x||!y)return !x&&!y;
    return x->id==y->id&&eq(x->ch[0],y->ch[0])&&eq(x->ch[1],y->ch[1]);
}
bool id_app(pNode x){
    if(x->id==-1){
        return id_app(x->ch[0]);
    }
    if(x->id==0){
        return id_app(x->ch[0])||id_app(x->ch[1])||eq(x->ch[0],lam(var(1)));
    }
    if(x->id>0){
        return 0;
    }
    assert(0);
}
bool has_eta(pNode x){
    if(x->id==-1){
        if(x->ch[0]->id==0){
            if(eq(var(1),x->ch[0]->ch[1])&&no_occur(x->ch[0]->ch[0],1))return 1;
        }
        return has_eta(x->ch[0]);
    }
    if(x->id==0){
        return has_eta(x->ch[0])||has_eta(x->ch[1]);
    }
    if(x->id>0){
        return 0;
    }
    assert(0);
}
int size(pNode x){
    if(x->id==-1){
        return 2+size(x->ch[0]);
    }
    if(x->id==0){
        return 2+size(x->ch[0])+size(x->ch[1]);
    }
    if(x->id>0){
        return 1+x->id;
    }
    assert(0);
}
bool beta_smaller(pNode x){
    if(x->id==-1){
        return beta_smaller(x->ch[0]);
    }
    if(x->id==0){
        if(x->ch[0]->id==-1){
            if(size(x)>size(subst(x->ch[0]->ch[0],x->ch[1])))return 1;
        }
        return beta_smaller(x->ch[0])||beta_smaller(x->ch[1]);
    }
    if(x->id>0){
        return 0;
    }
    assert(0);
}
bool lam_removable(pNode x){
    return x->id==-1&&no_occur(x->ch[0],1);
}
bool not_minimal(pNode x){
    return lam_removable(x)||id_app(x)||has_eta(x)||beta_smaller(x);
}

int n_node(pNode x){
    if(!x)return 0;
    return 1+n_node(x->ch[0])+n_node(x->ch[1]);
}
int height(pNode x){
    if(!x)return 0;
    return 1+std::max(height(x->ch[0]),height(x->ch[1]));
}

void print_var(std::ostream &os,int depth){
    if(depth<0){
        os<<"c"<<-depth;
        return;
    }
    if(depth<26){
        os<<char('a'+depth);
        return;
    }
    os<<"v"<<depth;
}
int fmt=1;
void print(std::ostream &os,pNode x,int depth=0,int parenthesis=0){
    if(!x){
        os<<"?";
        return;
    }
    /*if(eq(x,lam(app(var(1),var(1))))){
        os<<"Ω";
        return;
    }*/
    if(x->id==-1){
        if(parenthesis)os<<"(";
        if(fmt==1){
            os<<"\\";
            print_var(os,depth);
            os<<". ";
        }
        if(fmt==2)os<<"\\ ";
        print(os,x->ch[0],depth+1);
        if(parenthesis)os<<")";
        return;
    }
    if(x->id==0){
        if(parenthesis&2)os<<"(";
        print(os,x->ch[0],depth,1);
        os<<" ";
        print(os,x->ch[1],depth,2);
        if(parenthesis&2)os<<")";
        return;
    }
    if(x->id>0){
        if(fmt==1)print_var(os,depth-x->id);
        if(fmt==2)os<<x->id;
        return;
    }
    assert(0);
}
int table[1000][1000];
void to_table(pNode x,int i,int j){
    int w=n_node(x);
    if(x->id==-1){
        for(int k=0;k<w;++k){
            table[i][j+k]=1;
        }
        table[i][j]=2;
        to_table(x->ch[0],i+1,j+1);
        return;
    }
    if(x->id==0){
        for(int k=0;k<w;++k){
            table[i][j+k]=3;
        }
        to_table(x->ch[0],i+1,j);
        to_table(x->ch[1],i+1,j+n_node(x->ch[0])+1);
        return;
    }
    if(x->id>0){
        table[i][j]=2;
        for(int k=0;k<x->id;++k){
            while(i>0&&table[i-1][j]==3)table[--i][j]=4;
            if(i>0&&table[i-1][j]==1)table[--i][j]=(k+1==x->id?5:4);
        }
        return;
    }
    assert(0);
}
const char *table_str[6]={
    " ",//0
    "─",//1
    "└",//2
    "─",//3
    "┼",//4
    "┬",//5
};
void to_table(std::ostream &os,pNode x){
    int w=n_node(x);
    int h=height(x);
    if(w>1000||h>1000)return;
    for(int i=0;i<h;++i){
        for(int j=0;j<w;++j){
            table[i][j]=0;
        }
    }
    to_table(x,0,0);
    for(int i=0;i<h;++i){
        os<<"> ";
        for(int j=0;j<w;++j){
            int tp=table[i][j];
            assert(0<=tp&&tp<=5);
            os<<table_str[tp];
        }
        os<<'\n';
    }
}
std::ostream &operator<<(std::ostream &os,pNode x){
    print(os,x);
    return os<<'\n';
}

pNode reduce_1(pNode x,bool reduce_dup=false){
    ReduceCtx ctx(reduce_dup);
    x=ctx.reduce(x);
    if(ctx.redex)return x;
    return nullptr;
}
pNode reduce_n(pNode x,int n){
    try{
        for(int i=0;i<n;++i){
            auto y=reduce_1(x);
            if(!y)return x;
            x=y;
        }
    }catch(int e){
        return nullptr;
    }
    return nullptr;
}

int test(){
    pNode O=lam(lam(var(1)));
    pNode S=lam(lam(lam(app(var(2),app(app(var(3),var(2)),var(1))))));
    std::cout<<O;
    std::cout<<S;
    pNode v[10];
    v[0]=O;
    for(int i=1;i<10;++i)v[i]=app(S,v[i-1]);
    for(int i=0;i<10;++i){
        auto x=reduce_n(v[i],10000);
        v[i]=x;
        std::cout<<v[i];
    }
    pNode add=lam(lam(app(app(var(2),S),var(1))));
    pNode mul=lam(lam(app(app(var(2),app(add,var(1))),O)));
    std::cout<<add;
    std::cout<<mul;
    std::cout<<reduce_n(app(app(add,v[3]),v[5]),10000);
    std::cout<<reduce_n(app(app(mul,v[3]),v[2]),10000);
    pNode true_=lam(lam(var(2)));
    pNode false_=lam(lam(var(1)));
    pNode and_=lam(lam(app(app(var(2),var(1)),false_)));
    std::cout<<true_;
    std::cout<<false_;
    std::cout<<reduce_n(app(app(and_,false_),false_),10000);
    std::cout<<reduce_n(app(app(and_,false_),true_),10000);
    std::cout<<reduce_n(app(app(and_,true_),false_),10000);
    std::cout<<reduce_n(app(app(and_,true_),true_),10000);
    /*pNode x=app(lam(lam(var(2))),lam(lam(var(1))));
    std::cout<<x;
    x=ReduceCtx().reduce(x);
    std::cout<<x;*/
    return 0;
}

enum DecideResult{
    HALT,NONHALT,UNKNOWN
};
bool check_loop(pNode x,int maxT){
    for(int n=1;;n<<=1){
        pNode x0=x;
        for(int i=0;i<n;++i){
            if(!--maxT)return 0;
            x=reduce_1(x);
            if(!x)return 0;
            while(lam_removable(x))x=x->ch[0];
            if(eq(x0,x))return 1;
        }
    }
    return 0;
}
int max_size=0;
DecideResult decide(pNode x){
    if(auto res=reduce_n(x,100)){
        max_size=std::max(max_size,size(res));
        return HALT;
    }
    try{
        if(check_loop(x,256))return NONHALT;
    }catch(int e){}
    return UNKNOWN;
}
bool heu_loop(pNode x,int maxT,bool reduce_dup){
    int sz0=n_node(x);
    int szs[maxT]{};
    try{
        for(int i=0;i<maxT;++i){
            x=reduce_1(x,reduce_dup);
            if(!x)return 0;
            int sz1=n_node(x);
            szs[i]=sz1-sz0;
            //std::cout<<i<<": "<<(sz1-sz0)<<'\n';
            sz0=sz1;
        }
    }catch(int e){
        return 0;
    }
    for(int D=1;D*2<=maxT/2;++D){
        if(!memcmp(szs+maxT/2,szs+maxT/2+D,(maxT-maxT/2-D)*sizeof(int))){
            return 1;
        }
    }
    return 0;
}
struct Args;
typedef std::shared_ptr<Args> pArgs;
struct Args{
    pNode hd0;
    pArgs hd1;
    pArgs tl;
};
pArgs Args_cons(pNode hd0,pArgs hd1,pArgs tl){
    return std::make_shared<Args>(Args{hd0,hd1,tl});
}
pArgs Args_cons0(pArgs tl){
    return Args_cons(nullptr,nullptr,tl);
}
std::pair<pNode,pArgs> Args_nth(pArgs args,int n){
    while(n>0){
        assert(args);
        args=args->tl;
        --n;
    }
    assert(args);
    return {args->hd0,args->hd1};
}
int n_indent=0;
struct Indent{};
std::ostream &operator<<(std::ostream &os,Indent){
    for(int i=0;i<n_indent;++i)os<<"> ";
    return os;
}
std::ostream &operator<<(std::ostream &os,pArgs args){
    if(!args)return os;
    ++n_indent;
    os<<Indent()<<args->hd0;
    os<<args->hd1;
    --n_indent;
    os<<args->tl;
    return os;
}
bool check_halt_v2(pNode x0,bool dbg=0,int T=1e4){
    std::vector<std::tuple<pNode,bool,pArgs>> stk;
    stk.emplace_back(x0,false,nullptr);
    auto ret=[&](pNode c0,bool v0,pArgs args0){
        if(stk.empty())return 1;
        if(!v0)c0=nullptr,args0=nullptr;
        auto [x,v,args]=stk.back();
        stk.pop_back();
        if(c0&&c0->id==-1){
            stk.emplace_back(c0->ch[0],v,Args_cons(x,args,args0));
        }else{
            stk.emplace_back(x,false,args);
        }
        return 0;
    };
    for(;;){
        assert(!stk.empty());
        auto [x,v,args]=stk.back();
        stk.pop_back();
        if(T--<=0)return 0;
        if(x->id==-1){
            if(v){
                if(ret(x,v,args))break;
            }else{
                stk.emplace_back(x->ch[0],v,Args_cons0(args));
            }
            continue;
        }
        if(x->id==0){
            stk.emplace_back(x->ch[1],v,args);
            stk.emplace_back(x->ch[0],true,args);
            continue;
        }
        if(x->id>0){
            auto [c0,args0]=Args_nth(args,x->id-1);
            if(!c0){
                if(ret(c0,v,args0))break;
            }else{
                stk.emplace_back(c0,v,args0);
            }
            continue;
        }
        assert(0);
    }
    return 1;
}
namespace CTL{
typedef int32_t id_t;
template<class T>
struct IdAlloc{
	std::map<T,id_t> id;
	std::vector<const T*> idr;
	id_t get_id(const T &x,bool &upd_flag){
		auto [it,flag]=id.emplace(x,idp());
		if(flag){
            idr.emplace_back(&(it->first));
            upd_flag=1;
        }
        return it->second;
	}
	const T &at(id_t i)const{
		return *idr.at(i);
	}
	id_t idp()const{
		return (id_t)idr.size();
	}
};
struct CTL{
    IdAlloc<std::tuple<pNode,id_t,id_t>> args[10];
    //args[n] : id<n> <-> (pNode,id<n-1>,id<n>)
    std::map<id_t,id_t> prev[10];
    //prev[n] : id<n> -> id<n-1>
    std::map<id_t,std::set<id_t>> next;
    //next : id<NG_n-1> -> id<NG_n>
    int stk_NG_n,NG_n,T,usedT=0,n_upd=0;
    bool upd_flag=0,dbg;
    CTL(int stk_NG_n,int NG_n,int T,bool dbg=0):stk_NG_n(stk_NG_n),NG_n(NG_n),T(T),dbg(dbg){}
    typedef std::vector<std::tuple<pNode,bool,id_t>> stk_t;
    void print_Args(std::ostream &os,id_t a,int n,int var_id=1){
        if(a==-1)return;
        if(a==-2){
            os<<"...\n";
            return;
        }
        auto [hd0,hd1,tl]=args[n].at(a);
        ++n_indent;
        os<<Indent();
        print_var(os,-var_id);
        os<<" := "<<hd0;
        print_Args(os,hd1,n-1);
        --n_indent;
        print_Args(os,tl,n,var_id+1);
    }
    void print_stk(std::ostream &os,const stk_t &stk){
        os<<"stk:\n";
        for(const auto [x,v,args]:stk){
            os<<(v?"whnf":"nf")<<": "<<x;
            print_Args(os,args,NG_n);
        }
        os<<"end\n\n";
    }
    id_t get_prev(id_t x,int n){
        if(prev[n].count(x))return prev[n][x];
        id_t ret;
        if(x<0)ret=x;
        else if(n<=0)ret=-2;
        else{
            auto [hd0,hd1,tl]=args[n].at(x);
            ret=Args_cons(hd0,hd1,get_prev(tl,n),n-1);
        }
        upd_flag=1;
        if(n==NG_n)next[ret].insert(x);
        return prev[n][x]=ret;
    }
    id_t Args_cons(pNode hd0,id_t hd1,id_t tl,int n){
        //(hd0,hd1,tl) : (pNode,id<n>,id<n>)
        assert(n>=0);
        return args[n].get_id({hd0,get_prev(hd1,n),tl},upd_flag);
    }
    id_t Args_cons0(id_t tl,int n){
        return Args_cons(nullptr,-1,tl,n);
    }
    std::pair<pNode,id_t> Args_nth(id_t a,int n){
        // returns (hd0,hd1) : (pNode,id<NG_n-1>)
        while(n>0){
            assert(a>=0);
            a=std::get<2>(args[NG_n].at(a));
            --n;
        }
        assert(a>=0);
        auto [hd0,hd1,tl]=args[NG_n].at(a);
        return {hd0,hd1};
    }
    std::map<stk_t,std::set<std::tuple<pNode,bool,id_t,stk_t>>> stk_pop_;
    std::set<stk_t> stk_visited;
    std::deque<stk_t> stk_q;
    std::set<std::tuple<pNode,bool,id_t,stk_t>> stk_pop(const stk_t &stk){
        if(stk.empty())throw int(0);
        return stk_pop_[stk];
    }
    stk_t stk_push0(const stk_t &stk,pNode x,bool v,id_t args){
        if(T--<=0)throw int(1);
        ++usedT;
        auto stk1=stk;
        stk1.emplace_back(x,v,args);
        if(stk1.size()>(size_t)stk_NG_n)stk1.erase(stk1.begin());
        if(stk_pop_[stk1].emplace(x,v,args,stk).second){
            upd_flag=1;
            ++n_upd;
        }
        return stk1;
    }
    void stk_push(const stk_t &stk,pNode x,bool v,id_t args){
        auto stk1=stk_push0(stk,x,v,args);
        if(dbg){
            std::cout<<"reach:\n";
            print_stk(std::cout,stk1);
        }
        if(stk_visited.insert(stk1).second){
            if(dbg)std::cout<<"new!\n\n";
            stk_q.push_back(stk1);
            upd_flag=1;
        }
    }
    void step(const stk_t &stk){
        if(dbg){
            std::cout<<"check:\n";
            print_stk(std::cout,stk);
        }
        auto ret=[this](const stk_t &stk,pNode c0,bool v0,id_t args0){
            if(stk.empty())throw int(0);
            if(!v0)c0=nullptr,args0=-1;
            for(const auto [x,v,args,stk]:stk_pop(stk)){
                if(c0&&c0->id==-1){
                    stk_push(stk,c0->ch[0],v,Args_cons(x,args,args0,NG_n));
                }else{
                    stk_push(stk,x,false,args);
                }
            }
        };
        for(const auto [x,v,args,stk]:stk_pop(stk)){
            if(x->id==-1){
                if(v){
                    ret(stk,x,v,args);
                }else{
                    stk_push(stk,x->ch[0],v,Args_cons0(args,NG_n));
                }
                continue;
            }
            if(x->id==0){
                auto stk1=stk_push0(stk,x->ch[1],v,args);
                stk_push(stk1,x->ch[0],true,args);
                continue;
            }
            if(x->id>0){
                auto [c0,args0_]=Args_nth(args,x->id-1);
                auto nxt=next[args0_];
                if(dbg){
                    std::cout<<"c0: "<<c0;
                    std::cout<<"from<n-1>\n";
                    print_Args(std::cout,args0_,NG_n-1);
                }
                for(auto args0:nxt){
                    if(dbg){
                        std::cout<<"to<n>\n";
                        print_Args(std::cout,args0,NG_n);
                    }
                    if(!c0){
                        ret(stk,nullptr,false,-1);
                    }else{
                        stk_push(stk,c0,v,args0);
                    }
                }
                continue;
            }
            assert(0);
        }
    }
    bool check_nonhalt(pNode x0){
        if(dbg){
            std::cout<<"CTL: "<<x0;
        }
        stk_push({},x0,false,-1);
        try{
            for(;;){
                upd_flag=0;
                for(size_t i=0;i<stk_q.size();++i){
                    step(stk_q[i]);
                }
                if(!upd_flag){
                    //if(usedT>10000)std::cerr<<usedT<<" "<<n_upd<<" : "<<x0;
                    return 1;
                }
            }
        }catch(int e){
            return 0;
        }
    }
};
}
void for_each_expr(int n,int depth,std::function<void(pNode)> f){
    if(n>=2){
        for_each_expr(n-2,depth+1,[&](pNode x){
            f(lam(x));
        });
    }
    if(n>=4){
        for_each_expr(n-4,depth,[&](pNode x){
            for_each_expr(n-2-size(x),depth,[&](pNode y){
                f(app(x,y));
            });
        });
    }
    for(int i=1;i<=depth&&i<n;++i){
        f(var(i));
    }
}

int main(){
    for(int n=0;;++n){
        uint64_t n_tot=0,n_halt=0,n_nonhalt=0,n_fail=0;
        uint64_t n_tot0=0;
        max_size=0;
        long tt=clock();
        for_each_expr(n,0,[&](pNode x){
            if(size(x)<n)return;
            ++n_tot0;
            if(not_minimal(x))return;
            ++n_tot;
            switch(decide(x)){
                case HALT:{
                    ++n_halt;
                    #if 0
                    assert(check_halt_v2(x));
                    int args[][3]={
                        {1,2,10000},
                        {2,1,100000},
                        {2,2,100000},
                        {3,3,10000},
                        {4,4,10000}
                    };
                    for(auto [a,b,c]:args){
                        if(CTL::CTL(a,b,c,0).check_nonhalt(x)){
                            std::cerr<<x;
                            CTL::CTL(a,b,c,1).check_nonhalt(x);
                            std::cout.flush();
                            assert(0);
                        }
                    }
                    #endif
                    break;
                }
                case NONHALT:{
                    ++n_nonhalt;
                    if(check_halt_v2(x)){
                        check_halt_v2(x,true);
                        std::cout.flush();
                        assert(0);
                    }
                    break;
                }
                case UNKNOWN:{
                    #if 1
                    assert(!check_halt_v2(x,false,100));
                    if(CTL::CTL(2,2,5000000,0).check_nonhalt(x)){
                        ++n_nonhalt;
                        //assert(!check_halt_v2(x,false,1000000));
                        return;
                    }
                    if(check_halt_v2(x,false,1000000)){
                        ++n_halt;
                        return;
                    }
                    if(CTL::CTL(2,1,5000000,0).check_nonhalt(x)){
                        ++n_nonhalt;
                        return;
                    }
                    //if(heu_loop(x,30,false))return;
                    //if(heu_loop(x,30,true))return;

                    auto x0=x;
                    if(lam_removable(x0))std::cerr<<"lam_removable: ";
                    else if(id_app(x0))std::cerr<<"id_app: ";
                    else if(has_eta(x0))std::cerr<<"has_eta: ";
                    else if(beta_smaller(x0))std::cerr<<"beta_smaller: ";
                    std::cerr<<x0;
                    #if 0
                    constexpr int maxT=30;
                    int sz0=n_node(x);
                    std::cout<<x0;
                    to_table(std::cout,x0);

                    x=x0;
                    sz0=n_node(x);
                    int szs[maxT]{};
                    try{
                        for(int i=0;i<maxT;++i){
                            x=reduce_1(x,false);
                            assert(x);
                            int sz1=n_node(x);
                            szs[i]=sz1-sz0;
                            sz0=sz1;
                            if(n_node(x)>200)break;
                            std::cout<<i<<": "<<x;
                            to_table(std::cout,x);
                        }
                    }catch(int e){}
                    for(int i=0;i<maxT;++i)printf("(%d)",szs[i]);
                    printf("\n");
                    puts("\n\n");
                    check_halt_v2(x0,true,100);
                    #endif

                    #endif
                    ++n_fail;
                    break;
                }
            }
        });
        fprintf(stderr,"%d: %lu/%lu/%lu/%lu/%lu  %gs\n",n,n_tot0,n_tot,n_halt,n_nonhalt,n_fail,(clock()-tt)*1./CLOCKS_PER_SEC);
    }
    return 0;
}