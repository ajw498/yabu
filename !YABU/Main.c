/*
	Backup
	© Alex Waugh 2000

	$Id: Main.c,v 1.2 2000-11-04 17:51:52 AJW Exp $
*/

#include "MemCheck:MemCheck.h"

#include "OSLib:osgbpb.h"
#include "OSLib:fileraction.h"
#include "OSLib:wimp.h"
#include "OSLib:hourglass.h"

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

#define TASKNAME "Backup"

#define BUFFER_SIZE 1024
#define HASHTABLE_INCREMENT 1024

#define Error(s) {\
	fprintf(stderr,"%s\n",s);\
	xhourglass_smash();\
	exit(EXIT_FAILURE);\
}

#define E(x) {\
	os_error *err=x;\
	if (err!=NULL) Error(err->errmess);\
}

static struct {
	int traverseimages;
} config={0};

static FILE *listfile=NULL,*oldlistfile=NULL;

struct hashentry {
	bits load_addr;
	bits exec_addr;
	unsigned int size;
	char *filename;
};

static struct hashentry **hashtable=NULL;
static int hashtableentries=0,hashtablesize=0;
static char *srcdir=NULL,*destdir=NULL;

static int GenerateKey(char *filename, int size)
/*generate a hash table key for given filename*/
{
	int len, i, key = 0;
	
	len = strlen(filename);
	for (i=0; i<len; i++) key += filename[i];
	return key % size;
}

static void InsertIntoHash(struct hashentry **hashptr, int size, struct hashentry *entry)
/*insert into hash table*/
{
	int key;
	
	key = GenerateKey(entry->filename,size);
	while (hashptr[key]) {
		key++;
		if (key>=size) key = 0;
	}
	
	hashptr[key] = entry;
}

static void InsertEntry(struct hashentry *entry) {
/* insert a structure into the hash table, increasing hash table size if needed*/
	int i;
	
	if ((hashtableentries*4)/3>hashtablesize) {
		/*increase the size of the hash table*/
		struct hashentry **newhash;
		
		newhash = malloc((hashtablesize+HASHTABLE_INCREMENT)*sizeof(struct hashentry *));
		if (!newhash) return;
		for (i=0; i<hashtablesize+HASHTABLE_INCREMENT; i++) newhash[i] = NULL;
		for (i=0; i<hashtablesize; i++) {
		  if (hashtable[i]) InsertIntoHash(newhash,hashtablesize+HASHTABLE_INCREMENT,hashtable[i]);
		}
		hashtablesize += HASHTABLE_INCREMENT;
		free(hashtable);
		hashtable = newhash;
	}
	
	InsertIntoHash(hashtable,hashtablesize,entry);
	hashtableentries++;
}

static void ReadFile(void)
{
	char linebuffer[BUFFER_SIZE];
	char namebuffer[BUFFER_SIZE];
	bits load_addr,exec_addr;
	unsigned int size;
	struct hashentry *entry;
	int i;

	hashtablesize=HASHTABLE_INCREMENT;
	hashtableentries=0;
	hashtable=malloc(hashtablesize*sizeof(struct hashentry *));
	if (hashtable==NULL) Error("Not enough memory");
	for (i=0; i<hashtablesize; i++) hashtable[i] = NULL;
	if (oldlistfile) {
		while (!feof(oldlistfile)) {
			/*Get next line*/
			fgets(linebuffer,BUFFER_SIZE,oldlistfile);
			/*Skip comments*/
			if (linebuffer[0]=='#') continue;
			/*Parse line*/
			if (sscanf(linebuffer,"%X\t%X\t%u\t%s\n",&load_addr,&exec_addr,&size,namebuffer)==4) {
				entry=malloc(sizeof(struct hashentry));
				if (entry==NULL) Error("Not enough memory");
				entry->load_addr=load_addr;
				entry->exec_addr=exec_addr;
				entry->size=size;
				entry->filename=malloc(strlen(namebuffer)+1);
				if (entry->filename==NULL) Error("Not enough memory");
				strcpy(entry->filename,namebuffer);
				/*Put details in hash table*/
				InsertEntry(entry);
			}
		}
	}
}

static struct hashentry *FindEntry(char *filename)
{
	int key;

	key=GenerateKey(filename,hashtablesize);
	while (hashtable[key]) {
		if (strcmp(hashtable[key]->filename,filename)==0) return hashtable[key];
		key++;
		if (key>=hashtablesize) key = 0;
	}
	return NULL;
}

static void StartFilerAction(wimp_t fileractiontaskhandle,char *dest)
{
	wimp_event_no event;
	wimp_block pollblock;
	int poll=1;

	E(xfileractionsendstartoperation_copy(fileractiontaskhandle,(fileraction_VERBOSE | fileraction_FORCE/* | fileraction_FASTER*/),dest,strlen(dest)+1));

	/*Poll the wimp, and let Filer_Action do it's thing*/
	E(xhourglass_off());
	do {
		E(xwimp_poll((wimp_MASK_NULL | wimp_MASK_POLLWORD),&pollblock,NULL,&event));
		switch (event) {
			case wimp_USER_MESSAGE:
			case wimp_USER_MESSAGE_RECORDED:
				if (pollblock.message.action==message_QUIT) exit(EXIT_SUCCESS);
				if (pollblock.message.action==message_TASK_CLOSE_DOWN && pollblock.message.sender==fileractiontaskhandle) poll=0;
		}
	} while (poll);
	E(xhourglass_on());
}

static void TraverseDir(char *dir)
{
	int context=0;
	int numread;
	char srcdirbuffer[BUFFER_SIZE];
	char destdirbuffer[BUFFER_SIZE];
	char namebuffer[BUFFER_SIZE];
	osgbpb_info_list *namelist=(osgbpb_info_list *)namebuffer;
	wimp_t fileractiontaskhandle=0;

	/*Get full name of directory we are copying from and to*/
	if (dir) sprintf(srcdirbuffer,"%s.%s",srcdir,dir); else sprintf(srcdirbuffer,"%s",srcdir);
	if (destdir) {
		if (dir) sprintf(destdirbuffer,"%s.%s",destdir,dir); else sprintf(destdirbuffer,"%s",destdir);
	}

	/*Scan thought the directory contents*/
	do {
		E(xosgbpb_dir_entries_info(srcdirbuffer,namelist,1,context,BUFFER_SIZE,NULL,&numread,&context));
		if (numread!=0) {
			char buffer[BUFFER_SIZE];

			if (dir) sprintf(buffer,"%s.%s",dir,namelist->info[0].name); else sprintf(buffer,"%s",namelist->info[0].name);
			if (namelist->info[0].obj_type==fileswitch_IS_DIR || (config.traverseimages && namelist->info[0].obj_type==fileswitch_IS_IMAGE)) {
				if (destdir && fileractiontaskhandle) StartFilerAction(fileractiontaskhandle,destdirbuffer);
				fileractiontaskhandle=0;
				TraverseDir(buffer);
			} else {
				struct hashentry *entry;
				int copy=1;

				entry=FindEntry(buffer);
				if (entry) {
					if (namelist->info[0].load_addr==entry->load_addr && namelist->info[0].exec_addr==entry->exec_addr && namelist->info[0].size==entry->size) {
						/*file hasn't changed, so don't copy it*/
						copy=0;
					} else {
						/*File exists, but has changed so copy it*/
						copy=1;
					}
				} else {
					/*Doesn't exist in hash, so copy it*/
					copy=1;
				}
				if (copy) {
					if (listfile) fprintf(listfile,"%08X\t%08X\t%u\t%s\n",namelist->info[0].load_addr,namelist->info[0].exec_addr,namelist->info[0].size,buffer);
					if (destdir) {
						/*Start Filer_Action task if it isn't already started*/
						if (fileractiontaskhandle==0) {
							E(xwimp_start_task("Filer_Action",&fileractiontaskhandle));
							E(xfileraction_send_selected_directory(fileractiontaskhandle,srcdirbuffer));
						}
						E(xfileraction_send_selected_file(fileractiontaskhandle,namelist->info[0].name));
					}
				}
			}
		}
	} while (context!=osgbpb_NO_MORE);
	if (destdir && fileractiontaskhandle) StartFilerAction(fileractiontaskhandle,destdirbuffer);
	fileractiontaskhandle=0;
}

int main(int argc, char *argv[])
{
	time_t currenttime;
	int msgs[]={message_TASK_CLOSE_DOWN,message_QUIT};

	MemCheck_Init();
	MemCheck_RegisterArgs(argc,argv);
	MemCheck_InterceptSCLStringFunctions();
	MemCheck_SetStoreMallocFunctions(1);
	MemCheck_SetAutoOutputBlocksInfo(0);

	/*Initialise*/
	E(xwimp_initialise(wimp_VERSION_RO3,TASKNAME,(wimp_message_list *)msgs,NULL,NULL));
	E(xhourglass_on());

	/*Sort out command line arguments*/
	if (argc!=5) Error("Usage: "TASKNAME" srcdir destdir oldlist newlist");
	if (strcmp(argv[3],"none")!=0) {
		oldlistfile=fopen(argv[3],"r");
		if (oldlistfile==NULL) Error("Unable to open old list file");
	}
	if (strcmp(argv[1],"none")==0) Error("Source directory cannot be none");
	srcdir=argv[1];
	if (strcmp(argv[2],"none")!=0) destdir=argv[2];
	if (strcmp(argv[4],"none")!=0) {
		listfile=fopen(argv[4],"w");
		if (listfile==NULL) Error("Unable to open new list file");
	}

	/*Read contents of old list file into hash table*/
	ReadFile();

	/*Print date and directory to the file (for human reference only)*/
	time(&currenttime);
	if (listfile) fprintf(listfile,"#%s#%s\n",ctime(&currenttime),srcdir);

	/*Do the business*/
	TraverseDir(NULL);

	/*Concatenate old list file on end of new list file*/
	if (listfile && oldlistfile) {
		rewind(oldlistfile);
		while (!feof(oldlistfile)) {
			char buffer[BUFFER_SIZE];

			buffer[BUFFER_SIZE-1]='\0';
			if (fgets(buffer,BUFFER_SIZE-1,oldlistfile)) fputs(buffer,listfile);
		}
	}

	/*Tidy up*/
	if (listfile) fclose(listfile);
	if (oldlistfile) fclose(oldlistfile);
	E(xhourglass_off());
	return 0;
}

