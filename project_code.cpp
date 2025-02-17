#include <vector>
#include <map>
#include <unordered_map>
#include <cstdio>
#include <fstream>
#include <istream>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <algorithm>
#include <random>
#include <cstdlib>
#include <ctime>
#include <queue>
#include "cadical.hpp"
using namespace std;

//int www=0;
// 建立哈希表，实现string和编号的对应
unordered_map<string,int> net1;
unordered_map<string,int> net2;
int s_1_outputs;//net中第一组输出开始的序号
int s_2_inputs;
int s_2_outputs;
int s_xor;//xor开始的序号
int e;//xor结束的序号，总net的大小

//匹配检查
vector<int> occ_in_sequence;//第i个节点是否已经进入输入序列
vector<int> occ_out_sequence;
vector<int> input_sequence;//输入的排列
vector<int> output_sequence;//输出的排列，用于match检验

//支持集剪枝
vector<vector<int>> graph_1;//构成第一组的图的邻接表
vector<vector<int>> graph_re_1;//逆向图
vector<vector<int>> graph_2;
vector<vector<int>> graph_re_2;
vector<vector<int>> part_1_in;//矩阵，A[i][j]==1表示第j个输入的可影响输出个数为1
vector<vector<int>> part_2_in;
vector<vector<int> > part_1_out;
vector<vector<int> > part_2_out;
vector<int> support_set_number_in;//第i个元素为可影响输出数为i的支持集中有多少节点，1组2组相同
vector<int> support_set_number_out;
vector<int> in_support_set_1;//输入的支持集,第i个元素为第i个输入可影响的输出的数量
vector<int> in_support_set_2;
vector<int> out_support_set_1;//输出的支持集,第i个元素为第i个输出可被多少个输入影响
vector<int> out_support_set_2;    
int max_support_set_in=0;//最大输入支持集中有多少元素
int max_support_set_out=0;
vector<int> out_group_index_1;//第i个元素为第一组中第i个输出所在的支持集分组的序号
vector<int> out_group_index_2;
vector<vector<int>> dfs_in_1;
vector<vector<int>> dfs_out_1;
vector<vector<int>> dfs_in_2;
vector<vector<int>> dfs_out_2;
vector<int> done_in_1;
vector<int> done_out_1;
vector<int> done_in_2;
vector<int> done_out_2;

//随机仿真剪枝
vector<int> sim1_1;//sim1中1组的值（0,1）
vector<int> sim1_2;//sim1中2组的值（0,1）
vector<int> sim2_1;//sim2中1组的值（0,1）
vector<int> sim2_2;//sim2中2组的值（0,1）

vector<int> sim1_gate_1;//每个节点的值是由哪个门算出来的，因为一个门对应一个输出
vector<int> sim1_gate_2;
vector<int> in_degree_1;
vector<int> in_degree_2;
vector<int> reverse_effect_1;//第i个输入翻转后对多少个输出有影响
vector<int> reverse_effect_2;
vector<int> be_effected_1;//第i个输出被多少个输入翻转影响
vector<int> be_effected_2;

//分组与循环多次剪枝
int group_size_in;
int group_size_out;
vector<vector<int>> group1_in;
vector<vector<int>> group2_in;
vector<vector<int>> group1_out;
vector<vector<int>> group2_out;

//基于反例的sim1剪枝
vector<int> wr_example_1;
vector<int> wr_example_2;

enum GateType {
    Buf, Not,
    And, Or, Xor,
    Nand, Nor, Xnor
};

GateType gate_from_str(const string & s) {
    if (s == "buf") return Buf;
    if (s == "not") return Not;
    if (s == "and") return And;
    if (s == "or") return Or;
    if (s == "xor") return Xor;
    if (s == "nand") return Nand;
    if (s == "nor") return Nor;
    if (s == "xnor") return Xnor;
    throw std::runtime_error("Invalid gate type: " + s);
}

string gate_to_str(const GateType g) {
    switch(g) {
        case Buf: return "buf";
        case Not: return "not";
        case And: return "and";
        case Or: return "or";
        case Xor: return "xor";
        case Nand: return "nand";
        case Nor: return "nor";
        case Xnor: return "xnor";
    }
    throw std::runtime_error("Invalid gate type");
}

struct Gate {
    GateType type;
    string name;
    vector<string> inputs;
    string output;
};
struct gate_by_index//用index编号表示门，因为不知道为什么net哈希表有指针溢出情况，所以避免使用net
{
    int index;
    GateType type;
    vector<int> inputs;
    int output;
};

struct CircuitData {
    vector<string> ports;
    vector<string> inputs;
    vector<string> outputs;
    vector<string> wires;
    vector<Gate>   gates;
    vector<gate_by_index> gates_by_index;
    static CircuitData read_input(istream & in);
    void print(ostream & out);
};
CircuitData cir1;//分别对应两个电路
CircuitData cir2;
CircuitData CircuitData::read_input(istream & in) {
    string token;
    //     module   top      (
    in >> token >> token >> token;
    vector<string> ports;
    while(in >> token, token != ")") {
        if (token == ",") continue;
        ports.push_back(token);
    }
    //      ;
    in >> token;
    //    input    a1 , a2 , ...
    in >> token;
    vector<string> inputs;
    while(in >> token, token != ";") {
        if (token == ",") continue;
        inputs.push_back(token);
    }
    //    output   o1 , o2 , ...
    in >> token;
    vector<string> outputs;
    while(in >> token, token != ";") {
        if (token == ",") continue;
        outputs.push_back(token);
    }
    //    wire     w1 , w2 , ...
    //    or maybe no wire
    in >> token;
    vector<string> wires;
    if(token == "wire") {
        while(in >> token, token != ";") {
            if (token == ",") continue;
            wires.push_back(token);
        }
        in >> token;
    }
    vector<Gate> gates;
    while(token != "endmodule") {
        auto type = gate_from_str(token);
        string name;
        string output;
        //    g1        (        wi        ,
        in >> name >> token >> output >> token;
        vector<string> inputs;
        while(in >> token, token != ")") {
            if (token == ",") continue;
            inputs.push_back(token);
        }
        //     ;
        in >> token;
        auto gate = Gate {type, name, inputs, output};
        gates.push_back(gate);
        in >> token;
    }
    return CircuitData {ports, inputs, outputs, wires, gates};
}

void CircuitData::print(ostream & out) {
    out << "module top ( ";
    auto printCommaInterleave = [&out](const vector<string> & v) {
        for(size_t i = 0; i < v.size(); i++) {
            if(i) out << " , ";
            out << v[i];
        }
    };
    printCommaInterleave(ports);
    out << " ) ;\n";
    out << "  input ";
    printCommaInterleave(inputs);
    out << " ;\n";
    out << "  output ";
    printCommaInterleave(outputs);
    out << " ;\n";
    if(wires.size()) {
        out << "  wire ";
        printCommaInterleave(wires);
        out << " ;\n";
    }
    for(auto g: gates) {
        out << "  " << gate_to_str(g.type) << " ( ";
        out << g.output << " , ";
        printCommaInterleave(g.inputs);
        out << " ) ;\n";
    }
    out << "endmodule\n";
}

void build_network()//建立哈希表,一次性
{
    int i=0;
    //用图net储存节点
    int s_1_inputs=1;
    for(i=0;i<cir1.inputs.size();i++)//net1的输入从1开始,否则与add结束的0冲突
        net1[cir1.inputs[i]]=i+s_1_inputs;
    int s_1_wires=s_1_inputs+cir1.inputs.size();
    for(i=0;i<cir1.wires.size();i++)
        net1[cir1.wires[i]]=i+s_1_wires;
    s_1_outputs=s_1_wires+cir1.wires.size();
    for(i=0;i<cir1.outputs.size();i++)
        net1[cir1.outputs[i]]=i+s_1_outputs;
    s_2_inputs=s_1_outputs+cir1.outputs.size();
    for(i=0;i<cir2.inputs.size();i++)//net2的输入
        net2[cir2.inputs[i]]=i+s_2_inputs;
    int s_2_wires=s_2_inputs+cir2.inputs.size();
    for(i=0;i<cir2.wires.size();i++)
        net2[cir2.wires[i]]=i+s_2_wires;
    s_2_outputs=s_2_wires+cir2.wires.size();
    for(i=0;i<cir2.outputs.size();i++)
        net2[cir2.outputs[i]]=i+s_2_outputs;
    s_xor=s_2_outputs+cir1.outputs.size();
    e=s_xor+cir1.outputs.size();
    return;
}

void add_clause(CaDiCaL::Solver & solver, Gate& gate, unordered_map<string,int> & net)
//在solve中加入表达式约束，以门为约束
{
    switch(gate.type)
    {
        case Buf:
        solver.add(net[gate.inputs[0]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(-net[gate.inputs[0]]);solver.add(net[gate.output]);solver.add(0);
        break;
        case Not:
        solver.add(-net[gate.inputs[0]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[0]]);solver.add(net[gate.output]);solver.add(0);
        break;
        case And:
        solver.add(-net[gate.inputs[0]]);solver.add(-net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[0]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        break;
        case Or:
        solver.add(net[gate.inputs[0]]);solver.add(net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(-net[gate.inputs[0]]);solver.add(net[gate.output]);solver.add(0);
        solver.add(-net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        break;
        case Xor:
        solver.add(-net[gate.inputs[0]]);solver.add(net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[0]]);solver.add(-net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        solver.add(-net[gate.inputs[0]]);solver.add(-net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[0]]);solver.add(net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        break;
        case Nand:
        solver.add(-net[gate.inputs[0]]);solver.add(-net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[0]]);solver.add(net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        break;
        case Nor:
        solver.add(net[gate.inputs[0]]);solver.add(net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        solver.add(-net[gate.inputs[0]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(-net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        break;
        case Xnor:
        solver.add(-net[gate.inputs[0]]);solver.add(net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[0]]);solver.add(-net[gate.inputs[1]]);solver.add(-net[gate.output]);solver.add(0);
        solver.add(-net[gate.inputs[0]]);solver.add(-net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        solver.add(net[gate.inputs[0]]);solver.add(net[gate.inputs[1]]);solver.add(net[gate.output]);solver.add(0);
        break;
    }
}

void describe_gate_by_index()//建立gate_by_index
{
    for(int i=0;i<cir1.gates.size();i++)
    {
        gate_by_index gate;
        gate.index=i;
        gate.type=cir1.gates[i].type;
        for(int j=0;j<cir1.gates[i].inputs.size();j++)
            gate.inputs.push_back(net1[cir1.gates[i].inputs[j]]-1);
        //此处每个gate的输入已经为graph中节点的编号，对1组来说与net中的值相差1
        gate.output=net1[cir1.gates[i].output]-1;
        cir1.gates_by_index.push_back(gate);
    }
    for(int i=0;i<cir2.gates.size();i++)
    {
        gate_by_index gate;
        gate.index=i;
        gate.type=cir2.gates[i].type;
        for(int j=0;j<cir2.gates[i].inputs.size();j++)
            gate.inputs.push_back(net2[cir2.gates[i].inputs[j]]-s_2_inputs);
        //2组的输入与net中的值相差s_2_inputs
        gate.output=net2[cir2.gates[i].output]-s_2_inputs;
        cir2.gates_by_index.push_back(gate);
    }
}

void build_graph(CircuitData & cir,unordered_map<string,int> net ,vector<vector<int>> & graph,
vector<vector<int>> & graph_re, int minus)//全用序号表示，建立双向图
{
    for(int i=0;i<cir.gates.size();i++)//双向图
    {
        int out_index=net[cir.gates[i].output];
        for(int j=0;j<cir.gates[i].inputs.size();j++)
        {    
            graph[net[cir.gates[i].inputs[j]]-minus].push_back(out_index-minus);          
            graph_re[out_index-minus].push_back(net[cir.gates[i].inputs[j]]-minus);
        }
    }
    return;
}

void DFS(CircuitData & cir,int n ,vector<vector<int>> & dfs, vector<vector<int>> & graph,
 vector<int> &done,int low,int upper)//有多少个输出
{
    if(done[n]!=0)//已经计算过
        return;   
    bool node_is_leaf=true;
    for(int i=0;i<graph[n].size();i++)
    {
        node_is_leaf=false;
        DFS(cir,graph[n][i],dfs,graph,done,low,upper);
        int limit;
        if(low==0)//输入
            limit=cir.inputs.size();
        else//输出
            limit=cir.outputs.size();
        for(int j=0;j<limit;j++)
            if(dfs[graph[n][i]][j]!=0)
                dfs[n][j]=1;//可以被访问到,把值传回去
    }
    if(node_is_leaf==true)//叶子节点一定是输出
    {
        if(n>=low&&n<upper)
            dfs[n][n-low]=1;//第几个输出          
        done[n]=1;
        return;
    }    
    else if(n>=low&&n<upper)//虽然不是叶子节点但是也是输出
        dfs[n][n-low]=1;

    done[n]=1;
    return;
}

void build_support_set(CircuitData & cir,unordered_map<string,int> net,vector<vector<int>> graph,
vector<vector<int>> graph_re,vector<vector<int>> & dfs_in,vector<vector<int>> & dfs_out,
vector<int> & in_support_set,vector<int> & out_support_set,int minus,vector<int> & done_in,vector<int> & done_out )//DFS
{ 
    for(int i=0;i<cir.inputs.size();i++)
    {
        DFS(cir,net[cir.inputs[i]]-minus,dfs_in,graph,done_in,cir.inputs.size()+cir.wires.size(),cir.inputs.size()+cir.wires.size()+cir.outputs.size());
        for(int j=0;j<cir.outputs.size();j++)
            if(dfs_in[net[cir.inputs[i]]-minus][j]!=0)
                in_support_set[i]++;
        if(in_support_set[i]>max_support_set_in)//记录支持集的最大大小
            max_support_set_in=in_support_set[i];
    }   
    for(int i=0;i<cir.outputs.size();i++)
    {
        DFS(cir,net[cir.outputs[i]]-minus,dfs_out,graph_re,done_out,0,cir.inputs.size());
        for(int j=0;j<cir.inputs.size();j++)
            if(dfs_out[net[cir.outputs[i]]-minus][j]!=0)
                out_support_set[i]++;
        if(out_support_set[i]>max_support_set_out)
            max_support_set_out=out_support_set[i];
    }
} 

struct priority_struct//用于支持集细化剪枝
{
    int index;
    priority_queue<int> dfs_support;
};
int priority_queue_compare(priority_queue<int> a,priority_queue<int> b)
{
    while(!a.empty()&&!b.empty())
    {
        if(a.top()!=b.top())
            if(a.top()<b.top())
                return 1;
            else
                return -1;
        a.pop();
        b.pop();
    }
    return 0;
}
struct cmp
{
    bool operator()(priority_struct a,priority_struct b)
    {
        if(a.dfs_support.size()!=b.dfs_support.size())
            return a.dfs_support.size()<b.dfs_support.size();
        else if(priority_queue_compare(a.dfs_support,b.dfs_support)==1)
            return 1;
        else
            return 0;
    }
};

//支持集剪枝2
void support_set_pruning_2(CircuitData & cir,vector<vector<int>> & dfs_in,
vector<vector<int>> & group_in,vector<int> out_group_index)
{
    for(int i=0;i<group_size_in;i++)//第i个支持集
    {
        if(group_in[i].size()==1)//只有一个元素，不用细化
                continue;
       // cout<<i<<"::"<<endl;
        //求出每个元素的支持集queue
        priority_queue<priority_struct,vector<priority_struct>,cmp> q;
        for(int j=0;j<group_in[i].size();j++)//是一个输入节点的序号
        {
           //cout<<group_in[i][j]<<":";
            priority_queue<int> temp;
            for(int k=0;k<cir.outputs.size();k++)
                if(dfs_in[group_in[i][j]][k]==1)
                {
                    //cout<<k<<" index"<<out_group_index[k]<<" ";
                    temp.push(out_group_index[k]);  
                }
            //cout<<endl;
            priority_struct temp1;
            temp1.index=group_in[i][j];    
            temp1.dfs_support=temp;                
            q.push(temp1);
        }
        group_in[i].clear();
        //cout<<"clear"<<endl;
        int ref_place=i;
        priority_queue<int> ref_vector=q.top().dfs_support;
        int ref_index=q.top().index;
        q.pop();
        group_in[i].push_back(ref_index);
        //cout<<"ref"<<ref_index<<endl;
        while(!q.empty())
        {
            priority_queue<int> temp=q.top().dfs_support;
            int temp_index=q.top().index;
            //cout<<temp_index<<endl; 
            //for(int j=0;j<temp.size();j++)
              //  cout<<temp[j]<<" ";
            q.pop();       
            if(priority_queue_compare(temp,ref_vector)==0)
            {
                group_in[ref_place].push_back(temp_index);
                //cout<<"add "<<temp_index<<" to "<<ref_place<<endl;
            }
            else
            {
                vector<int> neww;//建一个新的支持集
                neww.push_back(temp_index);
                ref_vector=temp;
                ref_place=group_in.size();
                //cout<<"add "<<temp_index<<" to "<<ref_place<<endl;
                group_in.push_back(neww);
            }        
        }
    }
}

//simulation1
void sim_topo(CircuitData & cir,vector<vector<int>> & graph,
vector<int> & sim1,vector<int> & sim1_gate,vector<int> & in_degree)
//拓扑排序求输出的值
{
    for(int i=0;i<cir.inputs.size()+cir.wires.size()+cir.outputs.size();i++)
        in_degree[i]=0;     
    for(int i=0;i<cir.inputs.size()+cir.wires.size()+cir.outputs.size();i++)
        for(int j=0;j<graph[i].size();j++)
            in_degree[graph[i][j]]++;
    queue<int> topo;
    for(int i=0;i<cir.inputs.size()+cir.wires.size()+cir.outputs.size();i++)
        if(in_degree[i]==0)
            topo.push(i);
    while(!topo.empty())
    {
        //处理该节点
        int t=topo.front();
        topo.pop();
        int g=sim1_gate[t];
        if(g!=-1)//是门，不是输入     
        switch(cir.gates[g].type)
        {
            case Buf:
                sim1[t]=sim1[cir.gates_by_index[g].inputs[0]];
            break;
            case Not:
            if(sim1[cir.gates_by_index[g].inputs[0]]==1)
                sim1[t]=0;
            else
                sim1[t]=1;
            break;
            case And:
            if(sim1[cir.gates_by_index[g].inputs[0]]==1&&sim1[cir.gates_by_index[g].inputs[1]]==1)
               sim1[t]=1;
            else
                sim1[t]=0;
            break;
            case Or:
            if(sim1[cir.gates_by_index[g].inputs[0]]==1||sim1[cir.gates_by_index[g].inputs[1]]==1)
                sim1[t]=1;
            else
                sim1[t]=0;
            break;
            case Xor:
            if(sim1[cir.gates_by_index[g].inputs[0]]==sim1[cir.gates_by_index[g].inputs[1]])
                sim1[t]=0;
            else
                sim1[t]=1;
            break;
            case Nand:
            if(sim1[cir.gates_by_index[g].inputs[0]]==1&&sim1[cir.gates_by_index[g].inputs[1]]==1)
                sim1[t]=0;
            else
                sim1[t]=1;
            break;
            case Nor:
            if(sim1[cir.gates_by_index[g].inputs[0]]==1||sim1[cir.gates_by_index[g].inputs[1]]==1)
                sim1[t]=0;
            else
                sim1[t]=1;
            break;
            case Xnor:
            if(sim1[cir.gates_by_index[g].inputs[0]]==sim1[cir.gates_by_index[g].inputs[1]])
                sim1[t]=1;
            else
                sim1[t]=0;
            break;
        }
        //更新in_degree
        for(int i=0;i<graph[t].size();i++)
        {
            in_degree[graph[t][i]]--;
            if(in_degree[graph[t][i]]==0)
                topo.push(graph[t][i]);
        }
    }
    in_degree.clear();
    return;
}

void sim1(CircuitData & cir1, CircuitData & cir2, 
unordered_map<string,int> & net1,unordered_map<string,int> & net2,
vector<vector<int>> & graph_1,vector<vector<int>> & graph_2,
vector<vector<int>> & part_1,vector<vector<int>> & part_2)
{
    int m=0;
    for(int i=0;i<=max_support_set_in;i++)
    {
        m=rand()%2;
        //cout<<m<<endl;
        for(int j=0;j<part_1[i].size();j++)//每个part里的赋值相同
            if(part_1[i][j]==1)
                sim1_1[net1[cir1.inputs[j]]-1] = m;//也即sim1[j]=m
        for(int j=0;j<part_2[i].size();j++)
            if(part_2[i][j]==1)
                sim1_2[net2[cir2.inputs[j]]-s_2_inputs] = m;
    }
    //拓扑排序求输出的值，利用graph
    sim_topo(cir1,graph_1,sim1_1,sim1_gate_1,in_degree_1);
    sim_topo(cir2,graph_2,sim1_2,sim1_gate_2,in_degree_2);
    // for(int i=0;i<cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size();i++)
    //     cout<<i<<" "<<sim1_1[i]<<endl;
    // for(int i=0;i<cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size();i++)
    //     cout<<i<<" "<<sim1_2[i]<<endl;
    // for(int i=0;i<cir1.outputs.size();i++)
    //     cout<<i<<" "<<sim1_1[s_1_outputs+i-1]<<" "<<sim1_2[cir2.inputs.size()+cir2.wires.size()+i]<<endl;
}

void sim2_3(CircuitData & cir1, CircuitData & cir2,
vector<vector<int>> & graph_1,vector<vector<int>> & graph_2)
{  
    for(int i=0;i<cir1.inputs.size();i++)
    {
        sim2_1[i]=sim1_1[i];
        sim2_2[i]=sim1_2[i];
    }
    for(int i=0;i<cir1.inputs.size();i++)//轮流
    {
        if(sim1_1[i]==1)//翻转取值
            sim2_1[i]=0;
        else
            sim2_1[i]=1;
            //拓扑排序求输出的值，利用graph
        sim_topo(cir1,graph_1,sim2_1,sim1_gate_1,in_degree_1);
        for(int j=0;j<cir1.outputs.size();j++)
        {
            if(sim2_1[s_1_outputs+j-1]!=sim1_1[s_1_outputs+j-1])   
            {
                reverse_effect_1[i]++;
                be_effected_1[j]++;
            }
        }
        if(sim1_1[i]==1)//翻转回来
            sim2_1[i]=1;
        else
            sim2_1[i]=0;
    }
    for(int i=0;i<cir1.inputs.size();i++)
    {
        if(sim1_2[i]==1)//翻转取值
            sim2_2[i]=0;
        else
            sim2_2[i]=1;
            //拓扑排序求输出的值，利用graph
        sim_topo(cir2,graph_2,sim2_2,sim1_gate_2,in_degree_2);
        for(int j=0;j<cir1.outputs.size();j++)
        {
            if(sim2_2[cir2.inputs.size()+cir2.wires.size()+j]!=sim1_2[cir2.inputs.size()+cir2.wires.size()+j])
            {
                reverse_effect_2[i]++;
                be_effected_2[j]++;
            }
        }
        if(sim1_2[i]==1)//翻转回来
            sim2_2[i]=1;
        else
            sim2_2[i]=0;
    }
    return;
}

void circulation(CircuitData & cir1, CircuitData & cir2)
{
     //cout<<"circulation"<<endl;
    //  int qqq=0;
     while(1)
     {
        //qqq++;
        int lin=group1_in.size();
        int lout=group1_out.size();
        //cout<<"lin"<<lin<<"lout"<<lout<<endl;   
        std::fill(sim1_1.begin(), sim1_1.end(), 0);
        std::fill(sim1_2.begin(), sim1_2.end(), 0);
        std::fill(in_degree_1.begin(), in_degree_1.end(), 0);
        std::fill(in_degree_2.begin(), in_degree_2.end(), 0);
        sim1(cir1,cir2,net1,net2,graph_1,graph_2,part_1_in,part_2_in);
        //cout<<"sim1"<<endl;
        int l=group1_out.size();
    for(int i=0;i<l;i++)//基于sim1的分组
    {
        int ref=sim1_1[group1_out[i][0]+cir1.inputs.size()+cir1.wires.size()];
        vector<int> temp1;
        vector<int> temp2;
        int temp1_valid=0;
        int temp2_valid=0;
        for(int j=0;j<group1_out[i].size();j++)
        {
            if(ref!=sim1_1[group1_out[i][j]+cir1.inputs.size()+cir1.wires.size()])
            {            
                temp1.push_back(group1_out[i][j]);
                group1_out[i].erase(group1_out[i].begin()+j);
                temp1_valid=1;
                j--;
            }
        }
        for(int j=0;j<group2_out[i].size();j++)
        {
            if(ref!=sim1_2[group2_out[i][j]+cir2.inputs.size()+cir2.wires.size()])
            {              
                temp2.push_back(group2_out[i][j]);
                //cout<<"temp2"<<group2_out[i][j]<<endl;
                group2_out[i].erase(group2_out[i].begin()+j);          
                temp2_valid=1;
                j--;
            }
        }
        if(temp1_valid==1)
            group1_out.push_back(temp1);
        if(temp2_valid==1)
            group2_out.push_back(temp2);    
    }
    group_size_out=group1_out.size();
   // cout<<"sim1"<<endl;
    
// //随机仿真剪枝sim2    
    std::fill(sim2_1.begin(), sim2_1.end(), 0);
    std::fill(sim2_2.begin(), sim2_2.end(), 0);
    std::fill(reverse_effect_1.begin(), reverse_effect_1.end(), 0);
    std::fill(reverse_effect_2.begin(), reverse_effect_2.end(), 0);
    std::fill(be_effected_1.begin(), be_effected_1.end(), 0);
    std::fill(be_effected_2.begin(), be_effected_2.end(), 0);
    sim2_3(cir1,cir2,graph_1,graph_2);
    int r=group1_in.size();
    for(int i=0;i<r;i++)//基于sim2的分组
    {
        int ref=reverse_effect_1[group1_in[i][0]];
        //cout<<ref<<endl;
        vector<int> temp1;
        vector<int> temp2;
        int temp1_valid=0;
        int temp2_valid=0;
        for(int j=0;j<group1_in[i].size();j++)
        {
            if(ref!=reverse_effect_1[group1_in[i][j]])
            {            
                temp1.push_back(group1_in[i][j]);
                group1_in[i].erase(group1_in[i].begin()+j);
                temp1_valid=1;
                j--;
            }
        }
        for(int j=0;j<group2_in[i].size();j++)
        {
            if(ref!=reverse_effect_2[group2_in[i][j]])
            {              
                temp2.push_back(group2_in[i][j]);
                group2_in[i].erase(group2_in[i].begin()+j);          
                temp2_valid=1;
                j--;
            }
        }
        if(temp1_valid==1)
           group1_in.push_back(temp1);
        if(temp2_valid==1)
            group2_in.push_back(temp2);    
    }
    group_size_in=group1_in.size();

    int w=group1_out.size();
    for(int i=0;i<w;i++)//基于sim3的分组
    {
        int ref=be_effected_1[group1_out[i][0]];
        //cout<<ref<<endl;
        vector<int> temp1;
        vector<int> temp2;
        int temp1_valid=0;
        int temp2_valid=0;
        for(int j=0;j<group1_out[i].size();j++)
        {
            if(ref!=be_effected_1[group1_out[i][j]])
            {            
                temp1.push_back(group1_out[i][j]);
                group1_out[i].erase(group1_out[i].begin()+j);
                temp1_valid=1;
                j--;
            }
        }
        for(int j=0;j<group2_out[i].size();j++)
        {
            if(ref!=be_effected_2[group2_out[i][j]])
            {              
                temp2.push_back(group2_out[i][j]);
                group2_out[i].erase(group2_out[i].begin()+j);          
                temp2_valid=1;
                j--;
            }
        }
        if(temp1_valid==1)
           group1_out.push_back(temp1);
        if(temp2_valid==1)
            group2_out.push_back(temp2);    
    }
    group_size_out=group1_out.size();

    if(lin==group1_in.size()&&lout==group1_out.size())
        return;
    }
}

void add_constrain(CaDiCaL::Solver & solver,CircuitData & cir1, CircuitData & cir2)
{
    // 2的输入的string对应的编号
    for(int i=0;i<cir1.inputs.size();i++)
    {
        int j = input_sequence[i]; // 对应的cir2的输入
        net2[cir2.inputs[j]] = i+1;
    }
    // 加入cir1的门电路约束
    for(auto gate:cir1.gates)
        add_clause(solver,gate,net1);        
    // 加入cir2的门电路约束
    for(auto gate:cir2.gates)
        add_clause(solver,gate,net2);
    // 加入1和2的输出的异或约束
    for(int i=0;i<cir1.outputs.size();i++)
    {
        int j=output_sequence[i];
        solver.add(-net1[cir1.outputs[i]]);solver.add(-net2[cir2.outputs[j]]);solver.add(-(i+s_xor));solver.add(0);
        solver.add(-net1[cir1.outputs[i]]);solver.add(net2[cir2.outputs[j]]);solver.add(i+s_xor);solver.add(0);
        solver.add(net1[cir1.outputs[i]]);solver.add(-net2[cir2.outputs[j]]);solver.add(i+s_xor);solver.add(0);
        solver.add(net1[cir1.outputs[i]]);solver.add(net2[cir2.outputs[j]]);solver.add(-(i+s_xor));solver.add(0);
    }
    // 加入异或后到输出的约束
    for(int i=0;i<cir1.outputs.size();i++)
        solver.add(-(i+s_xor));
    solver.add(e);solver.add(0);      
    solver.add(-e);
    for(int i=0;i<cir1.outputs.size();i++)
        solver.add(i+s_xor);         
    solver.add(0);
    // 加入总的输出约束
    solver.add(e);solver.add(0);
}

bool solve_check(CaDiCaL::Solver & solver)
{
    auto res = solver.solve();
    if(res==20)
        return true;   
    else
    {
        for(int i=0;i<cir1.outputs.size();i++)
        {
            if(solver.val(i+s_1_outputs)>0)
                wr_example_1[i]=1;
            else
                wr_example_1[i]=0;
            if(solver.val(i+s_2_outputs)>0)
                wr_example_2[i]=1;
            else
                wr_example_2[i]=0;
            //cout<<wr_example_1[i]<<" "<<wr_example_2[i]<<endl;
        }
       // cout<<endl;
        return false;
    }
        
}

bool match_out(int m,int n)//m从0开始
{    
    //int reff_2=0;
    if(m==group_size_out)
    {
        CaDiCaL::Solver solver;
        for(int i=0;i<output_sequence.size();i++)
            cout<<output_sequence[i]<<" ";
        cout<<endl;
        add_constrain(solver,cir1,cir2);
        if(solve_check(solver))
            return true;
        else
        {         
            for(int i=0;i<group_size_out;i++)
            {
                const int reff=wr_example_1[group1_out[i][0]];
                // cout<<reff_1<<endl;
                // cout<<reff_2<<endl;
                vector<int> temp1;
                vector<int> temp2;
                for(int j=0;j<group1_out[i].size();j++)
                {
                    if(reff!=wr_example_1[group1_out[i][j]])
                    {                       
                        temp1.push_back(group1_out[i][j]);                      
                        group1_out[i].erase(group1_out[i].begin()+j);
                        j--;
                    }
                }
                for(int j=0;j<group2_out[i].size();j++)
                {
                    cout<<i<<" reff="<<reff<<endl;
                    if(reff!=wr_example_2[group2_out[i][j]])
                    {            
                        cout<<reff<<" "<<wr_example_2[group2_out[i][j]]<<endl;           
                        temp2.push_back(group2_out[i][j]);                      
                        group2_out[i].erase(group2_out[i].begin()+j);
                        cout<<group2_out[i][j]<<"in another group"<<endl;  
                        j--;
                    }
                     
                    // if(wr_example_1[group1_out[i][0]]!=wr_example_2[group2_out[i][j]])
                    // {                       
                    //     temp2.push_back(group2_out[i][j]);     
                 
                    //     group2_out[i].erase(group2_out[i].begin()+j);
                    //     j--;
                    // }
                }
                if(temp1.size()!=0)
                    group1_out.push_back(temp1);
                if(temp2.size()!=0)
                    group2_out.push_back(temp2);
            }
            cout<<group_size_out<<" "<<group1_out.size()<<" "<<group2_out.size()<<endl;
            if(group_size_out==group1_out.size())
             {
                return false;
             }
            else
            {
                group_size_out=group1_out.size();
                for(int i=0;i<group_size_out;i++)
                {
                    cout<<i<<":";
                    for(int j=0;j<group1_out[i].size();j++)
                        cout<<group1_out[i][j]<<" "<<group2_out[i][j]<<" ";
                    cout<<endl;
                }
                std::fill(occ_out_sequence.begin(), occ_out_sequence.end(), 0);
                std::fill(output_sequence.begin(), output_sequence.end(), 0);
                return match_out(0,0);
            }
        }   
    }
    else if(n==group1_out[m].size())
    {
        //cout<<"n full next m="<<m+1<<endl;
        return match_out(m+1,0);
    }    
    else
    {
        int i=group1_out[m][n];
        //cout<<m<<" "<<n<<" "<<i<<endl;
        for(int j=0;j<group2_out[m].size();j++)
        {
            int k=group2_out[m][j];
            //cout<<"k="<<k<<endl;
            if(occ_out_sequence[k]==1)
                continue;
            output_sequence[i]=k;
            occ_out_sequence[k]=1;
            if(match_out(m,n+1))
                return true;
            occ_out_sequence[k]=0;
        }
    }
    return false;
}

bool match_in(int m,int n)//m从0开始
{
    if(m==group_size_in)
    {
        cout<<"input_sequence:"<<endl;
        for(int i=0;i<input_sequence.size();i++)
            cout<<input_sequence[i]<<" ";
            cout<<endl;
        if(match_out(0,0))
            return true;         
    }
    else if(n==group1_in[m].size())
        return match_in(m+1,0);
    else
    {
        int i=group1_in[m][n];
        for(int j=0;j<group2_in[m].size();j++)
        {
            int k=group2_in[m][j];
            if(occ_in_sequence[k]==1)
                continue;
            input_sequence[i]=k;
            occ_in_sequence[k]=1;
            if(match_in(m,n+1))
                return true;
            occ_in_sequence[k]=0;
        }
    }
    return false;
}

int main(int argc, char ** argv) 
{
    string input_circuit_1 = argv[1];
    string input_circuit_2 = argv[2];
    ifstream in1(input_circuit_1);
    cir1 = CircuitData::read_input(in1);
    ifstream in2(input_circuit_2);
    cir2 = CircuitData::read_input(in2);

    //net1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size());
    input_sequence.resize(cir1.inputs.size(),0);
    occ_in_sequence.resize(cir2.inputs.size(),0);
    occ_out_sequence.resize(cir2.outputs.size(),0);
    output_sequence.resize(cir1.outputs.size(),0);
    build_network();//建立net
    //cout<<"network built"<<endl;
    describe_gate_by_index();//给门编号，以后不用再在net里寻找，这里的序号比net中的多1
    //cout<<"gate described"<<endl;

    //graph从0开始，与net差1
    graph_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size());
    graph_re_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size());
    graph_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size());
    graph_re_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size());
    build_graph(cir1,net1,graph_1,graph_re_1,1);
    build_graph(cir2,net2,graph_2,graph_re_2,s_2_inputs);
    //cout<<"graph bulit"<<endl;

//支持集剪枝
    in_support_set_1.resize(cir1.inputs.size(),0);//输入的支持集,可影响的输出的数量
    out_support_set_1.resize(cir1.outputs.size(),0);//输出的支持集
    in_support_set_2.resize(cir2.inputs.size(),0);//输入的支持集
    out_support_set_2.resize(cir2.outputs.size(),0);//输出的支持集
    dfs_in_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size(),vector<int> (cir1.outputs.size(),0));
    dfs_out_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size(),vector<int> (cir1.inputs.size(),0));
    dfs_in_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),vector<int> (cir2.outputs.size(),0));
    dfs_out_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),vector<int> (cir2.inputs.size(),0));
    //可影响的输入或输出在graph中的编号
    done_in_1.resize(cir2.inputs.size()+cir1.wires.size()+cir1.outputs.size(),0);
    done_out_1.resize(cir2.inputs.size()+cir1.wires.size()+cir1.outputs.size(),0);
    done_in_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),0);
    done_out_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),0);
    //是否已经计算过
    build_support_set(cir1,net1,graph_1,graph_re_1,dfs_in_1,dfs_out_1,in_support_set_1,out_support_set_1,1,done_in_1,done_out_1);
    build_support_set(cir2,net2,graph_2,graph_re_2,dfs_in_2,dfs_out_2,in_support_set_2,out_support_set_2,s_2_inputs,done_in_2,done_out_2);
    //cout<<"support_set_built"<<endl;
    // for(int i=0;i<cir1.inputs.size();i++)
    // {
    //     cout<<i<<":"<<endl;
    //     for(int j=0;j<dfs_in_1[i].size();j++)
    //         cout<<dfs_in_1[i][j]<<" ";
    //     cout<<endl;
    // }
    // for(int i=0;i<cir2.inputs.size();i++)
    // {
    //     cout<<i<<":"<<endl;
    //     for(int j=0;j<dfs_in_2[i].size();j++)
    //         cout<<dfs_in_2[i][j]<<" ";
    //     cout<<endl;
    // }
    out_group_index_1.resize(cir1.outputs.size(),0);
    out_group_index_2.resize(cir2.outputs.size(),0);
    part_1_in.resize(max_support_set_in+1,vector<int>(cir1.inputs.size(),0));//支持集大小一样的构成一个部分匹配
    part_2_in.resize(max_support_set_in+1,vector<int>(cir1.inputs.size(),0));
    part_1_out.resize(max_support_set_out+1,vector<int>(cir1.outputs.size(),0));
    part_2_out.resize(max_support_set_out+1,vector<int>(cir1.outputs.size(),0));
    support_set_number_in.resize(max_support_set_in+1,0);
    support_set_number_out.resize(max_support_set_out+1,0);
    //group1_out.resize(cir2.outputs.size()+1);
    //group2_out.resize(cir2.outputs.size()+1);
    for(int i=0;i<cir1.inputs.size();i++)
    {
        part_1_in[in_support_set_1[i]][i]=1;
        support_set_number_in[in_support_set_1[i]]++;
        part_2_in[in_support_set_2[i]][i]=1;
        support_set_number_in[in_support_set_2[i]]++;
    }
    for(int i=0;i<cir1.outputs.size();i++)
    {
        part_1_out[out_support_set_1[i]][i]=1;
        support_set_number_out[out_support_set_1[i]]++;
        part_2_out[out_support_set_2[i]][i]=1;
        support_set_number_out[out_support_set_2[i]]++;
    }
    for(int i=0;i<=max_support_set_in;i++)//基于支持集的分组
    {
        if(support_set_number_in[i]==0)
            continue;
        vector<int> temp1;
        vector<int> temp2;
        for(int j=0;j<cir1.inputs.size();j++)
        {
            if(part_1_in[i][j]==1)
                temp1.push_back(j);
            if(part_2_in[i][j]==1)
                temp2.push_back(j);
        }
        group1_in.push_back(temp1);
        group2_in.push_back(temp2);
    }
    for(int i=0;i<=max_support_set_out;i++)
    {
        if(support_set_number_out[i]==0)
            continue;
        vector<int> temp1;
        vector<int> temp2;
        int s1=group1_out.size();
        int s2=group2_out.size();
        for(int j=0;j<cir1.outputs.size();j++)
        {
            if(part_1_out[i][j]==1)
            {
                temp1.push_back(j);
                out_group_index_1[j]=s1;
            }
            if(part_2_out[i][j]==1)
            {
                temp2.push_back(j);
                out_group_index_2[j]=s2;
            }
        }
        group1_out.push_back(temp1);
        group2_out.push_back(temp2);
    }
    // for(int i=0;i<cir1.outputs.size();i++)
    //     cout<<i<<":"<<out_group_index_1[i]<<" "<<out_group_index_2[i]<<endl;
    group_size_in=group1_in.size();
    //支持集剪枝2
    support_set_pruning_2(cir1,dfs_in_1,group1_in,out_group_index_1);
    support_set_pruning_2(cir2,dfs_in_2,group2_in,out_group_index_2);
    // for(int i=0;i<group1_in.size();i++)
    // {
    //     cout<<i<<":";
    //     for(int j=0;j<group1_in[i].size();j++)
    //         cout<<group1_in[i][j]<<" ";
    //     cout<<endl;
    // }
    // for(int i=0;i<group2_in.size();i++)
    // {
    //     cout<<i<<":";
    //     for(int j=0;j<group2_in[i].size();j++)
    //         cout<<group2_in[i][j]<<" ";
    //     cout<<endl;
    // }
    for(int i=0;i<group1_out.size();i++)
    {
        cout<<i<<":";
        for(int j=0;j<group1_out[i].size();j++)
            cout<<group1_out[i][j]<<" ";
        cout<<endl;
    }
    for(int i=0;i<group2_out.size();i++)
    {
        cout<<i<<":";
        for(int j=0;j<group2_out[i].size();j++)
            cout<<group2_out[i][j]<<" ";
        cout<<endl;
    }

//随机仿真剪枝sim1
    sim1_gate_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size(),-1);
    sim1_gate_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),-1);
    for(int i=0;i<cir1.gates.size();i++)
    {
        int out_index=net1[cir1.gates[i].output]-1;
        sim1_gate_1[out_index]=i;
    }
    for(int i=0;i<cir2.gates.size();i++)
    {
        int out_index=net2[cir2.gates[i].output]-s_2_inputs;
        sim1_gate_2[out_index]=i;
    }

    sim1_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size(),0);
    sim1_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),0);
    in_degree_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size(),0);
    in_degree_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),0);
    //sim1(cir1,cir2,net1,net2,graph_1,graph_2,part_1_in,part_2_in);
    sim2_1.resize(cir1.inputs.size()+cir1.wires.size()+cir1.outputs.size(),0);
    sim2_2.resize(cir2.inputs.size()+cir2.wires.size()+cir2.outputs.size(),0);
    reverse_effect_1.resize(cir1.inputs.size(),0);
    reverse_effect_2.resize(cir2.inputs.size(),0);
    be_effected_1.resize(cir1.outputs.size(),0);
    be_effected_2.resize(cir2.outputs.size(),0);
    //circulation(cir1,cir2);
    //cout<<"sim1 ready"<<endl;
 
    

    occ_in_sequence.resize(cir1.inputs.size(),0);
    occ_out_sequence.resize(cir1.outputs.size(),0);
    wr_example_1.resize(cir1.outputs.size(),0);
    wr_example_2.resize(cir2.outputs.size(),0);
    if(match_in(0,0))//匹配
    {
        for(int i = 0; i < cir1.inputs.size(); i++) 
            cout << cir1.inputs[i] << " " << cir2.inputs[input_sequence[i]] << endl;               
        for(int i = 0; i < cir1.outputs.size(); i++) 
            cout << cir1.outputs[i] << " " << cir2.outputs[output_sequence[i]] << endl;
    }
    else
        cout<<"fail"<<endl;
    // for(int i=0;i<cir1.inputs.size();i++)
    //     cout<<input_sequence[i]<<" ";
    // cout<<endl;
    // for(int i=0;i<cir1.outputs.size();i++)
    //     cout<<output_sequence[i]<<" ";
    // cout<<endl;
    return 0;
}
