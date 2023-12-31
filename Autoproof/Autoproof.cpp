#include<cstdio>
#include<stack>
#include<string>
#include<iostream>
#include<vector>
#include<windows.h>
#define LEN 500
#define M 32769
using namespace std;

stack<char>sign;
vector<char>front[M];
vector<char>back[M];
vector<char>post;
bool error, node[M]; int maxi;
void initialize()
{
	error = 0; maxi = 0; post.clear();
	while (!sign.empty())sign.pop();
	for (int i = 0; i < M; i++)
	{
		front[i].clear();
		back[i].clear();
		node[i] = 0;
	}
}
void display()
{
	system("cls");
	printf("本程序用来判断输入命题逻辑公式的真伪\n符号：&代表合取，|代表析取，!代表否定，>代表蕴含，=代表双蕴含\n优先级：(), !, &, |, >, =\n命题用大写字母表示\n");
	system("pause");
}
void input()
{
	system("cls");
	printf("命题公式：");
	char c[LEN];
	cin.getline(c, LEN);
	int len = strlen(c);
	for (int i = 0; i < len; i++)
	{
		if (error)break;
		if (c[i] >= 'A' && c[i] <= 'Z')post.push_back(c[i]);
		else
			switch (c[i])
			{
				case '(':sign.push(c[i]); break;
				case '!':while (!sign.empty() && (sign.top() == '!')) { post.push_back(sign.top()); sign.pop(); }
						sign.push(c[i]); break;
				case '&':while (!sign.empty() && (sign.top() == '!' || sign.top() == '&')) { post.push_back(sign.top()); sign.pop(); }
						sign.push(c[i]); break;
				case '|':while (!sign.empty() && (sign.top() == '!' || sign.top() == '&' || sign.top() == '|')) { post.push_back(sign.top()); sign.pop(); }
						sign.push(c[i]); break;
				case '>':while (!sign.empty() && (sign.top() == '!' || sign.top() == '&' || sign.top() == '|' || sign.top() == '>')) { post.push_back(sign.top()); sign.pop(); }
						sign.push(c[i]); break;
				case '=':while (!sign.empty() && (sign.top() == '!' || sign.top() == '&' || sign.top() == '|' || sign.top() == '>' || sign.top() == '=')) { post.push_back(sign.top()); sign.pop(); }
						sign.push(c[i]); break;
				case ')':while (sign.top() != '(') { post.push_back(sign.top()); sign.pop(); }
						sign.pop(); break;
				default:error = 1; break;
			}
	}
	while (!sign.empty()) { post.push_back(sign.top()); sign.pop(); }
}
void copy(int dep)
{
	for (int i = 0; i < front[dep / 2].size(); i++)front[dep].push_back(front[dep / 2][i]);
	for (int i = 0; i < back[dep / 2].size(); i++)back[dep].push_back(back[dep / 2][i]);
}
void simplify(int dep, bool fr);
void and_(int dep, bool fr)
{
	if (fr)
	{
		post.pop_back();
		simplify(dep, 1);
		simplify(dep, 1);
	}
	else
	{
		node[dep] = 1;
		post.pop_back();
		simplify(dep * 2, 0);
		simplify(dep * 2 + 1, 0);
	}
}
void or_(int dep, bool fr)
{

	if (fr)
	{
		node[dep] = 1;
		post.pop_back();
		simplify(dep * 2, 1);
		simplify(dep * 2 + 1, 1);
	}
	else
	{
		post.pop_back();
		simplify(dep, 0);
		simplify(dep, 0);
	}
}
void non(int dep, bool fr)
{
	if (fr)
	{
		post.pop_back();
		simplify(dep, 0);
	}
	else
	{
		post.pop_back();
		simplify(dep, 1);
	}
}
void implication(int dep, bool fr)
{
	if (fr)
	{
		node[dep] = 1;
		post.pop_back();
		simplify(dep * 2, 1);
		simplify(dep * 2 + 1, 0);
	}
	else
	{
		post.pop_back();
		simplify(dep, 0);
		simplify(dep, 1);
	}
}
void double_impli(int dep, bool fr)
{
	vector<char>tmp;
	tmp.clear(); node[dep] = 1;
	if (fr)
	{
		post.pop_back(); tmp.clear();
		for (int i = 0; i < post.size(); i++)tmp.push_back(post[i]);
		simplify(dep * 2, 1); post.clear();
		for (int i = 0; i < tmp.size(); i++)post.push_back(tmp[i]);
		simplify(dep * 2 + 1, 0);
		tmp.clear();
		for (int i = 0; i < post.size(); i++)tmp.push_back(post[i]);
		simplify(dep * 2, 1); post.clear();
		for (int i = 0; i < tmp.size(); i++)post.push_back(tmp[i]);
		simplify(dep * 2 + 1, 0);
	}
	else
	{
		post.pop_back(); tmp.clear();
		for (int i = 0; i < post.size(); i++)tmp.push_back(post[i]);
		simplify(dep * 2, 1); post.clear();
		for (int i = 0; i < tmp.size(); i++)post.push_back(tmp[i]);
		simplify(dep * 2 + 1, 0);
		tmp.clear();
		for (int i = 0; i < post.size(); i++)tmp.push_back(post[i]);
		simplify(dep * 2, 0); post.clear();
		for (int i = 0; i < tmp.size(); i++)post.push_back(tmp[i]);
		simplify(dep * 2 + 1, 1);
	}
}
void simplify(int dep, bool fr)
{
	if (dep != 1)copy(dep);
	if (post.back() >= 'A' && post.back() <= 'Z')
		if (fr) { front[dep].push_back(post.back()); post.pop_back(); }
		else { back[dep].push_back(post.back()); post.pop_back(); }
	else
		switch (post.back())
		{
			case '&':and_(dep, fr); break;
			case '|':or_(dep, fr); break;
			case '!':non(dep, fr); break;
			case '>':implication(dep, fr); break;
			case '=':double_impli(dep, fr); break;
		}
	maxi = dep > maxi ? dep : maxi;
}
bool check()
{
	bool repeat[130] = { 0 };
	for (int i = 1; i <= maxi; i++)
	{
		if (node[i])
		{
			for (int j = 0; j < front[i].size(); j++)
			{
				front[i * 2].push_back(front[i][j]);
				front[i * 2 + 1].push_back(front[i][j]);
			}
			for (int j = 0; j < back[i].size(); j++)
			{
				back[i * 2].push_back(back[i][j]);
				back[i * 2 + 1].push_back(back[i][j]);
			}
		}
		else
		{
			bool ifre = 0;
//			if (!back[i].size())ifre = 1;
			for (int j = 0; j < front[i].size(); j++)repeat[(int)front[i][j]] = 1;
			for (int j = 0; j < back[i].size(); j++)
				if (repeat[(int)back[i][j]])ifre = 1;
			if (!ifre)return 0;
		}
	}
	return 1;
}
int main()
{
	display();
	while (1)
	{
		initialize();
		input();
		if (error)printf("input error!\n");
		else
		{
			simplify(1, 0);
			if (check())printf("True\n");
			else printf("False\n");
		}
		printf("回车继续，输入q退出\n");
		if (getchar() == 'q')break;
	}
}