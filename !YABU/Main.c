/*
	Backup
	© Alex Waugh 2000

	$Id: Main.c,v 1.1 2000-11-03 21:09:57 AJW Exp $
*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>


#include "OSLib:osgbpb.h"

#define BUFFER_SIZE 1024

static struct {
	int traverseimages;
} config={0};

static FILE *listfile=NULL;

struct hashentry {
	bits load_addr;
	bits exec_addr;
	unsigned int size;
	char *filename;
};

static struct hashentry hashtable[1];

static void TraverseDir(char *prefix,char *dir)
{
	os_error *err=NULL;
	osgbpb_info_list *namelist=malloc(BUFFER_SIZE);
	int context=0;
	int numread;
	char dirbuffer[BUFFER_SIZE];

	sprintf(dirbuffer,"%s.%s",prefix,dir);
	do {
		err=xosgbpb_dir_entries_info(dirbuffer,namelist,1,context,BUFFER_SIZE,NULL,&numread,&context);
		if (err==NULL) {
			if (numread!=0) {
				fprintf(listfile,"%08X\t%08X\t%u\t%s.%s\n",namelist->info[0].load_addr,namelist->info[0].exec_addr,namelist->info[0].size,dir,namelist->info[0].name);
				if (namelist->info[0].obj_type==fileswitch_IS_DIR || (config.traverseimages && namelist->info[0].obj_type==fileswitch_IS_IMAGE)) {
					char buffer[BUFFER_SIZE];

					sprintf(buffer,"%s.%s",dir,namelist->info[0].name);
					TraverseDir(prefix,buffer);
				}
			}
		} else {
			fprintf(stderr,"Error: %s",err->errmess);
			return;
		}
	} while (context!=osgbpb_NO_MORE);
}

int main(void)
{
	time_t currenttime;
	char *prefix="ADFS::4.$";
	
	time(&currenttime);
	listfile=fopen("ADFS::4.$.list","w");
	fprintf(listfile,"%s%s\n",ctime(&currenttime),prefix);
	TraverseDir(prefix,"BSD");
	fclose(listfile);
	return 0;
}

