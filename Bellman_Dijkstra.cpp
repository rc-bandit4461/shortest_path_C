#include<stdio.h>
#include<stdlib.h>
#include<string.h>
typedef struct nd
{
 int visited; // utilisée pour dijkstra, chaque noeud est visit?une seule fois
 int *preds; // va contenir la liste des predecesseurs de ce noeud
 int npreds; // nombre de predecesseurs (taille du tableau preds);
 int *succs; //va contenir la liste des successeurs de ce noeud
 char name[50]; // nom du sommet
 int nsuccs; // nombre de successeurs( taille du tableau succs)
int distinf; // au lieu de faire une valeur specifique representant l'infini,
 				  // on va mettre un boolean qui va indiquer si la distance presente dans 
 				  // la matrice des valeurs est l'infini ou non.
 int isDebut;	//indique le sommet de debut( la source )
} noeud;
typedef noeud* Noeud;
Noeud *pNods;
FILE *graphFile;
int nbrNods,**matVals,*dists,*preds; // preds va contenir les predecesseurs de chaque sommet apres lexecution de bellman/dijkstra
//nbrNods et le nombre de noeuds saisi par l'utilisateur
// matVals est la matrice qui contient les valeurs des arcs
// dists va contenir les distances du sommets vers le sommet de debut
// 
// 
void dist(int nod,int dist,int isinfini){ //permet d'affecter une distance a un sommet
		pNods[nod]->distinf=isinfini;   //nod represente le noeud qu'on souhaite chanquer sa distance depuis la source
		dists[nod] = dist;				//dist represente la distance qu'on souhaite affecter
}										//isinfini est le boolean qui indique si la distance est infini ou non.
									    
void freeAll(){ // va etre utilisée à la fin du programme pour liberer l'espace utilisée par les tableaux dynamiques
	int i;
	for(i = 0;i<nbrNods;i++){
		free(dists);
		free(preds);
		free(pNods[i]->succs);
		free(pNods[i]->preds);
		free(pNods[i]);
		free(matVals[i]);
	}
	free(matVals);
	free(pNods);
}
void Initialisation(int s){
	int i;
	for(i =0;i<nbrNods;i++){
		dist(i,0,1); // distance ====> infini, 
		preds[i] = -1; // predecesseur non encore défini.
		pNods[i]->isDebut = 0; // ce n'est pas le sommet du debut
	}
	dist(s,0,0);
	preds[s] = s; 
	pNods[s]->isDebut = 1; // sommet de debut (depuis qu'on va aller)
}

int Bellmann(int s){
	int i,j,stable,pred;
	int k = 0;
			Initialisation(s);
			while(1){
				stable = 1; // si stable ne change pas, donc les distances n'ont pas changées dans les derniereres deux itérations
				for (i = 0; i < nbrNods; i++)
				//if(pNods[i]->isDebut == 0){
					if(s!=i){
					for(j=0;j<pNods[i]->npreds;j++){
						pred = pNods[i]->preds[j];
						if(pNods[pred]->distinf == 0 && (pNods[i]->distinf == 1 || (dists[i]>dists[pred]+matVals[pred][i]))){
						 // si dist(i)>dist(pred(i)+l(pred(i),i))
							dist(i,dists[pred]+matVals[pred][i],0); //nouvelle distance pour le sommet i
							preds[i]=pred; //remplacement du nouveau predecesseur de i
							stable = 0; // un changement detecté ==> on aura une nouvelle iteration
						}
					}
				}
				k++;
				// sortir du boucle si le graphe est stable ou k a attent le nombre de noeud(circuit absorbant dans ce cas)
				if(stable == 1 || k == nbrNods) break; 
			}
			return  k == nbrNods ? 0:1; // k == nbrNods ?? => circabs = VRAI
}
int ExistValeurNegative(int **mat,int n){ // retourne 0 si toutes les arcs ont des valeurs positives
	int i,j;
	for(i = 0;i<n;i++)
		for(j = 0;j<n;j++)
			if(mat[i][j]<0) return 1;
		return 0;
}
void Relacher(int i,int j,int **l){
	if(pNods[i]->distinf == 0 && (pNods[j]->distinf == 1 || dists[j]>dists[i]+l[i][j])){
		dist(j,dists[i]+l[i][j],0);
		preds[j] = i;
	}
}
int findnonvisitedsmallestdistance(){ 					// recherche le noeud non encore été visité 			
	int i,smallestid;									//ayant la distance la plus petite du sommet
														// de début lors de l'algorithme de Dijkstra
	for(i = 0;i<nbrNods;i++); //Rechercher tout dabord un sommet non visité.
			if(pNods[i]->visited == 0 && pNods[i]->distinf == 0) break;
		smallestid = i;
	for(i = smallestid+1;i<nbrNods;i++)
			if(pNods[i]->visited == 0 && pNods[i]->distinf == 0 && dists[i]<dists[smallestid])
				smallestid = i;
			return smallestid;
}
void dijkstra(int s,int dest){		// Algorithme de dijkstra du noeud S(debut) vers la destination(dest)
	int i,recent,succ;
	Initialisation(s);
	for(i = 0;i<nbrNods;i++)
			pNods[i]->visited = 0;
			pNods[s]->visited = 1;
			recent = s;
		while(pNods[dest]->visited == 0){
			for(i = 0;i<pNods[recent]->nsuccs;i++){
				succ = pNods[recent]->succs[i];
				if(pNods[succ]->visited == 0)
					Relacher(recent,succ,matVals);
			}
					recent = findnonvisitedsmallestdistance();
					pNods[recent]->visited = 1;
		}
}
void afficherchemin(int s,int dest){ //fonction affichant le chemin critique voulu
	if(s!=dest){
			 afficherchemin(s,preds[dest]);
			 printf("->%s",pNods[dest]->name);
			 fprintf(graphFile, "-> _%d ",dest); //afficher le chemin dans le fichier
	}
	else	{
		printf("%s",pNods[s]->name);
	fprintf(graphFile, "_%d",s); //afficher le chemin dans le fichier
	}
}
void plusCoursChemin(int s,int dest,int algoid){ // permet d'afficher le plus court chemein en utilisant
		int length=0,*t = (int*)malloc(sizeof(int)),i;				// algoid == 0 => bellmann ; algoid == 1 => dijkstra
		if(algoid == 0){ printf("\nBellman-Ford:");
		if(!Bellmann(s)){
			 printf("\nIl existe un circuit absorbant.");
			 free(t);
			 return;
		}
	}
	else {printf("\nDijkstra:");
	if(!ExistValeurNegative(matVals,nbrNods)) // existence d'une valeur negative ?????
			dijkstra(s,dest);  // sinon, executer dijkstra
	else {
		printf("\nIl existe une ou plusieurs valeurs negatives.\n"); //si oui, afficher un message et terminer.
		free(t);
		return;
	}
	}
			//si le programme arrive ici, cad qu'il n'ya pas de circuits absorbant en cas de Bellmann,
			// ou il n'ya pas d'arcs de valeur négative deans le cas de Dijkstra
			printf("Le plus cours chemin de %s a %s est le suivant : ",pNods[s]->name,pNods[dest]->name);
			afficherchemin(s,dest);
			fprintf(graphFile, " [color=\"green\"];\n");
			printf("\nIl est de longueur :%d",dists[dest]);
			free(t);
}

Noeud CreateNode(int i){ // retourne un noeud(un sommet)
	Noeud nodz = (Noeud)malloc(sizeof(noeud));
	printf("saisir nom du noeud %d: ",i);
	fflush(stdin);
	gets(nodz->name);
	 nodz->visited = 0;	
 nodz->preds=NULL;	
 nodz->npreds=0;	
 nodz->succs=NULL;	
 nodz->nsuccs=0;	
nodz->distinf=0;
nodz->isDebut;	
	return nodz;
}
Noeud* CreateNods(int n){ // creer lensemble des noeuds
	Noeud* p = (Noeud*)malloc(sizeof(Noeud)*n);int i;
	for(i = 0;i<n;i++)
		{
			p[i]=CreateNode(i);
			fprintf(graphFile, "_%d [label=\"%s\"];\n",i,p[i]->name);
		}
	return p;
}
void AjouterSucc(int i,int j){ 	   // Ajout j dans la liste des successeurs de i,s'il n'est pas ajouté
	int k;						   //  j est le noeud successeur de i
	if(pNods[i]->nsuccs == 0){
			pNods[i]->succs = (int*)malloc(sizeof(int));
			(pNods[i]->nsuccs)++;
			(pNods[i]->succs)[0]=j;
}
	else {for(k = 0;k<pNods[i]->nsuccs;k++) if(j == *(pNods[i]->succs+k)) return; // si j est deja dans 
			realloc(pNods[i]->succs,sizeof(int)*((pNods[i]->nsuccs+1)));		  // la liste des 
			(pNods[i]->nsuccs)++;												  //successeurs
				*(pNods[i]->succs+pNods[i]->nsuccs-1) = j;
	}
}
void AjouterPred(int i,int j){ //  ajout j and la liste des prédecesseurs de i s'il n'est pas dèja ajouté
	int k;					
	if(pNods[i]->npreds == 0){
			pNods[i]->preds = (int*)malloc(sizeof(int));
			(pNods[i]->npreds)++;
			(pNods[i]->preds)[0]=j;
}
	else {	for(k = 0;k<pNods[i]->npreds;k++) if(j == *(pNods[i]->preds+k)) return; // si j est deja
			realloc(pNods[i]->preds,sizeof(int)*((pNods[i]->npreds+1)));			//dans la liste des
			(pNods[i]->npreds)++;													//predecesseurs
				*(pNods[i]->preds+pNods[i]->npreds-1) = j;
	}
}
int **allocatesapcemat(int n){ //Retourne une matrice de dimension nxn initialisée à 0. (calloc)
	int **t,i;
		t = (int**)malloc(sizeof(int*)*n);
		for(i = 0;i<n;i++)
			t[i]=(int*)calloc(n,sizeof(int));
		return t;
}
int **matvalcreate(int n){ //creation de la matrice de valeurs (ponderations)
	int i,**t,j;
	char c;
	t = allocatesapcemat(n);
	for(i = 0;i<n;i++){
			
		for(j = 0;j<n;j++) if(j!=i){
			
			printf("\nya till un arc de %s vers %s ? taper (N/n) sinon :",pNods[i]->name,pNods[j]->name);
			fflush(stdin);
			scanf("%c",&c);
			if(c!='n' && c!='N') {
					printf("saisir la valeur entre %s et %s :",pNods[i]->name,pNods[j]->name);
					fflush(stdin);
					scanf("%d",&t[i][j]);
					AjouterSucc(i,j);
					AjouterPred(j,i);
					fprintf(graphFile, "_%d -> _%d [label=\"%d\"];\n",i,j,t[i][j]);
			}

		}		
	}
return t;
}
void affichtab(int *t,int n){
	int i;
	for(i =0;i<n;i++)
			printf("%d ",t[i]);
}	
int findNoeud(char *z){ // noeud dont le nom est z ?? si oui retourner son numero, sinon retourner -1
	int i;
	for(i = 0;i<nbrNods;i++)
		if(strcmp(z,pNods[i]->name) == 0) return i;
	return -1; 
}
void ChercherPlusCoursChemin(){
	int sourceid,destid,algoid;
	char source[50],destination[50];
	E:printf("Quel Algorith a utiliser ? (0:Bellmann, 1:Dijkstra) : ");
	scanf("%d",&algoid);
	if(algoid!= 0 && algoid!=1) {
		printf("saisir une des valeurs suggerees.\n");
		goto E;
	}
	printf("saisir le nom de la source : ");
	fflush(stdin);
	gets(source);
	printf("saisir le nom de la destination : ");
	fflush(stdin);
	gets(destination);
	sourceid = findNoeud(source);
	if(sourceid == -1) {
		printf("Le noeud %s nexiste pas.",source);
		return ;
	}
	destid = findNoeud(destination);
	if(destid == -1){
		 printf("Le noeud %s nexiste pas.",destination);
		 return ;
	}
	plusCoursChemin(sourceid,destid,algoid);
}
int main(int argc, char const *argv[])
{	
	printf("saisir nombre de sommets : ");
	char str[50];
	F:scanf("%d",&nbrNods); // nombre de noeuds : il faut verifier si nbrNods >=1
	if(nbrNods <3 ){
		printf("Il faut saisir un nombre strictement superieur a 2 : ");goto F;
	}
	printf("saisir le nom du fichier dot : ");
	fflush(stdin);
	gets(str);
	graphFile = fopen(str,"w+");
	if(graphFile == NULL) {
		printf("erreur de creation de fichier.");
		exit(-1);
	}
	fprintf(graphFile, "digraph G {\n");
	pNods = CreateNods(nbrNods);
	matVals = matvalcreate(nbrNods);
	dists = (int*)malloc(sizeof(int)*nbrNods);
	preds = (int*)malloc(sizeof(int)*nbrNods);
	ChercherPlusCoursChemin();
	fprintf(graphFile,"}");
	fclose(graphFile);
	printf("\ntableau des distances : ");
	affichtab(dists,nbrNods);
	printf("\ntableau des predecesseurs : ");
	affichtab(preds,nbrNods);
	freeAll();
	return 0;
}
