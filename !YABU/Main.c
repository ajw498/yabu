/*
	YABU   Yet Another Backup Utility
	© Alex Waugh 2000


	This program is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.
	
	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.
	
	You should have received a copy of the GNU General Public License
	along with this program; if not, write to the Free Software
	Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


	$Id: Main.c,v 1.17 2002-12-05 23:10:22 ajw Exp $
*/

#ifdef MemCheck_MEMCHECK
#include "MemCheck:MemCheck.h"
#endif
#ifdef HierProf_PROFILE
#include "HierProf:HierProf.h"
#endif

#include "oslib/osgbpb.h"
#include "oslib/osfscontrol.h"
#include "oslib/osfile.h"
#include "oslib/fileraction.h"

#include "Desk/Window.h"
#include "Desk/Error2.h"
#include "Desk/Event.h"
#include "Desk/EventMsg.h"
#include "Desk/Handler.h"
#include "Desk/Hourglass.h"
#include "Desk/Icon.h"
#include "Desk/Menu.h"
#include "Desk/Msgs.h"
#include "Desk/Filing.h"
#include "Desk/DeskMem.h"
#include "Desk/Resource.h"
#include "Desk/Screen.h"
#include "Desk/Template.h"
#include "Desk/Str.h"
#include "Desk/File.h"
#include "Desk/Sprite.h"

#include "AJWLib/Window.h"
#include "AJWLib/Menu.h"
#include "AJWLib/File.h"
#include "AJWLib/Msgs.h"
#include "AJWLib/Error2.h"

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <time.h>
#include <string.h>

#define DIRPREFIX "YABU"
#define VERSION "1.05 (5-Dec-2002)"
#define AUTHOR "© Alex Waugh 2000"

#define iconbarmenu_INFO 0
#define iconbarmenu_HELP 1
#define iconbarmenu_QUIT 2

#define icon_OK 16
#define icon_CANCEL 15
#define icon_IMAGES 5
#define icon_FASTER 17
#define icon_SRC 6
#define icon_SRCDRAG 11
#define icon_DEST 7
#define icon_DESTDRAG 12
#define icon_EXCLUDE 8
#define icon_EXCLUDEDRAG 13
#define icon_EXIST 9
#define icon_NEW 10
#define icon_NEWDRAG 14
#define icon_SAVEDEFAULT 18
#define icon_VERBOSE 19
#define icon_MD5 20

#define status_DIR 0
#define status_READ 2
#define status_COPIED 4
#define status_SKIP 6
#define status_CANCEL 7

#define MAXICONLENGTH 256
#define MAXEXCLUDES 256
#define MAXSRCS 256
#define BUFFER_SIZE 10240
#define MAX_BUFFER_ENTRIES 1000
#define HASHTABLE_INCREMENT 10240
#define MD5LEN 32

#define CheckOS(x) Desk_Error2_CheckOS((Desk_os_error *)x)

#define MultiTask() {\
 	Desk_Event_mask.data.null=0;\
	Desk_Hourglass_Off();\
	Desk_Event_Poll();\
	Desk_Hourglass_On();\
	Desk_Event_mask.data.null=1;\
	lastpoll=os_read_monotonic_time();\
}

#define CHECKPOLL (os_read_monotonic_time()>lastpoll+10)

static struct {
	char *src;
	char *dest;
	char *exclude;
	char *existinglist;
	char *newlist;
	Desk_bool images;
	Desk_bool faster;
	Desk_bool verbose;
	Desk_bool md5;
} defaults;

static FILE *listfile=NULL,*oldlistfile=NULL;

struct hashentry {
	bits load_addr;
	bits exec_addr;
	unsigned int size;
	char md5[MD5LEN];
	char *filename;
};

static struct hashentry **hashtable=NULL;
static int hashtableentries=0,hashtablesize=0;
static char *srcdir=NULL,*destdir=NULL;
static Desk_bool traverseimages,running=Desk_FALSE;
static int faster=0, verbose=1, md5=0;
static Desk_icon_handle dragicon;

static Desk_bool startimmediatly=Desk_FALSE;
static Desk_bool keeppolling=Desk_FALSE;
static Desk_task_handle fileractiontaskhandle=0;
static int numfilesread,numfilescopied;
static int numexcludes=0;
static char *excludes[MAXEXCLUDES];
static int numsrcs=0;
static char *srcdirs[MAXSRCS];

static Desk_window_handle proginfowin,mainwin,statuswin;
static Desk_menu_ptr iconbarmenu;
static char *taskname=NULL,*errbad=NULL;
static os_t lastpoll=0;

static int GenerateKey(char *filename, int size)
/*generate a hash table key for given filename*/
{
	int len, i, key = 0, mult;
	
	len = strlen(filename);
	mult = size/(len+1);
	for (i=0; i<len; i++) key += mult*i*filename[i];
	return key % size;
}

static void InsertIntoHash(struct hashentry **hashptr, int size, struct hashentry *entry)
/*insert into hash table*/
{
	int key;
	
	key = GenerateKey(entry->filename,size);
	while (hashptr[key]) {
		if (strcmp(hashptr[key]->filename,entry->filename)==0) return; /*Newer entry for same file already exists in hash, so don't create a duplicate*/
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
	int count=0;
	int validline;
	char md5sum[MD5LEN];

	MultiTask();
	if (!running) return;

	hashtablesize=HASHTABLE_INCREMENT;
	hashtableentries=0;
	hashtable=Desk_DeskMem_Malloc(hashtablesize*sizeof(struct hashentry *));
	for (i=0; i<hashtablesize; i++) hashtable[i] = NULL;
	if (oldlistfile) {
		AJWLib_Msgs_SetText(statuswin,status_DIR,"Status.1:");
		while (!feof(oldlistfile)) {
			/*Get next line*/
			fgets(linebuffer,BUFFER_SIZE,oldlistfile);
			/*Skip comments*/
			if (linebuffer[0]=='#') continue;
			/*Parse line*/
			if (linebuffer[8]=='\t') {
				validline=sscanf(linebuffer,"%X\t%X\t%u\t%s\n",&load_addr,&exec_addr,&size,namebuffer)==4;
				memset(md5sum,0,MD5LEN);
			} else {
				validline=sscanf(linebuffer,"%s\t%s\n",md5sum,namebuffer)==2;
				size=load_addr=exec_addr=0;
			}
			if (validline) {
				entry=Desk_DeskMem_Malloc(sizeof(struct hashentry));
				entry->load_addr=load_addr;
				entry->exec_addr=exec_addr;
				entry->size=size;
				memcpy(entry->md5,md5sum,MD5LEN);
				entry->filename=Desk_DeskMem_Malloc(strlen(namebuffer)+1);
				strcpy(entry->filename,namebuffer);
				/*Put details in hash table*/
				InsertEntry(entry);

				count++;
				if (CHECKPOLL) {
					Desk_Icon_SetInteger(statuswin,status_READ,count);
					MultiTask();
					if (!running) return;
				}
			}
		}
	}
	MultiTask();
	if (!running) return;
}

static struct hashentry *FindEntry(char *filename)
{
	int key;

	key=GenerateKey(filename,hashtablesize);
	while (hashtable[key]) {
		if (strcmp(hashtable[key]->filename,filename)==0) {
			return hashtable[key];
		}
		key++;
		if (key>=hashtablesize) key = 0;
	}
	return NULL;
}

static Desk_bool TaskCloseDownMsg(Desk_event_pollblock *block,void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.message.header.sender==fileractiontaskhandle) keeppolling=Desk_FALSE;
	return Desk_TRUE;
}

static void StartFilerAction(char *dest)
{
	CheckOS(xfileractionsendstartoperation_copy((wimp_t)fileractiontaskhandle,(verbose | fileraction_FORCE | faster),dest,strlen(dest)+1));
	/*Poll the wimp, and let Filer_Action do it's thing*/
	keeppolling=Desk_TRUE;
	while (keeppolling) {
		Desk_Hourglass_Off();
		Desk_Event_Poll();
		lastpoll=os_read_monotonic_time();
		Desk_Hourglass_On();
		if (!running) return;
	}
}

static Desk_bool SkipClick(Desk_event_pollblock *block,void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.select) {
		keeppolling=Desk_FALSE;
		Desk_Wimp_SetIconState(statuswin,status_SKIP,1<<23,1<<23); /*Delete icon*/
		Desk_Icon_ForceWindowRedraw(statuswin,status_SKIP);
	}
	return Desk_TRUE;
}

static void TraverseDir(char *dir)
{
	int context=0;
	int numread;
	char srcdirbuffer[BUFFER_SIZE];
	char destdirbuffer[BUFFER_SIZE];
	char namebuffer[BUFFER_SIZE];
	osgbpb_info_list *namelist=NULL;


	/*Get full name of directory we are copying from and to*/
	if (dir) sprintf(srcdirbuffer,"%s.%s",srcdir,dir); else sprintf(srcdirbuffer,"%s",srcdir);
	if (destdir) {
		if (dir) sprintf(destdirbuffer,"%s.%s",destdir,dir); else sprintf(destdirbuffer,"%s",destdir);
	}

	Desk_Icon_SetText(statuswin,status_DIR,srcdirbuffer);

	/*Scan thought the directory contents*/
	do {
		os_error *err;

		namelist=(osgbpb_info_list *)namebuffer;
		err=xosgbpb_dir_entries_info(srcdirbuffer,namelist,MAX_BUFFER_ENTRIES,context,BUFFER_SIZE,NULL,&numread,&context);
		if (err) {
			Desk_Icon_SetText(statuswin,status_READ,err->errmess);
			Desk_Wimp_SetIconState(statuswin,status_SKIP,0,1<<23); /*Undelete icon*/
			keeppolling=Desk_TRUE;
			while (keeppolling) {
				Desk_Hourglass_Off();
				Desk_Event_Poll();
				Desk_Hourglass_On();
				if (!running) return;
			}
			return;
		}
		while (numread>0) {
			char buffer[BUFFER_SIZE];
			char canonical[BUFFER_SIZE];
			Desk_bool exclude=Desk_FALSE;
			int i;

			sprintf(buffer,"%s.%s",srcdirbuffer,namelist->info[0].name);
			if (xosfscontrol_canonicalise_path(buffer,canonical,NULL,NULL,BUFFER_SIZE,&i)) strcpy(canonical,buffer);
			for (i=0;i<numexcludes;i++) {
				if (Desk_stricmp(canonical,excludes[i])==0) {
					exclude=Desk_TRUE;
					break;
				}
			}
			if (dir) sprintf(buffer,"%s.%s",dir,namelist->info[0].name); else sprintf(buffer,"%s",namelist->info[0].name);
			if (!exclude) {
				if (namelist->info[0].obj_type==fileswitch_IS_DIR || (traverseimages && namelist->info[0].obj_type==fileswitch_IS_IMAGE)) {
					if (destdir && fileractiontaskhandle) StartFilerAction(destdirbuffer);
					fileractiontaskhandle=0;
					Desk_Icon_SetInteger(statuswin,status_COPIED,numfilescopied);
					Desk_Icon_SetInteger(statuswin,status_READ,numfilesread);
					TraverseDir(buffer);
					if (!running) return;
					Desk_Icon_SetText(statuswin,status_DIR,srcdirbuffer);
				} else {
					struct hashentry *entry;
					int copy=1;
					char md5buf[BUFFER_SIZE];
					FILE *output;

					numfilesread++;
					entry=FindEntry(buffer);
					if (md5) {
						sprintf(md5buf,"md5sum %s > <Wimp$Scrap>",canonical);
						Desk_Wimp_StartTask(md5buf);
						output=AJWLib_File_fopen("<Wimp$Scrap>","r");
						fread(md5buf,MD5LEN,1,output);
						fclose(output);
					}
					if (entry) {
						if (md5) {
							if (memcmp(md5buf,entry->md5,MD5LEN)==0) copy=0;
						} else {
							if (namelist->info[0].load_addr==entry->load_addr && namelist->info[0].exec_addr==entry->exec_addr && namelist->info[0].size==entry->size) {
								/*file hasn't changed, so don't copy it*/
								copy=0;
							} else {
								/*File exists, but has changed so copy it*/
								copy=1;
							}
						}
					} else {
						/*Doesn't exist in hash, so copy it*/
						copy=1;
					}
					if (copy) {
						if (listfile) {
							if (md5) {
								fwrite(md5buf,MD5LEN,1,listfile);
								fprintf(listfile,"\t%s\n",buffer);
							} else {
								fprintf(listfile,"%08X\t%08X\t%u\t%s\n",namelist->info[0].load_addr,namelist->info[0].exec_addr,namelist->info[0].size,buffer);
							}
						}
						if (destdir) {
							numfilescopied++;
							/*Start Filer_Action task if it isn't already started*/
							if (fileractiontaskhandle==0) {
								Desk_Wimp_StartTask3("Filer_Action",&fileractiontaskhandle);
								CheckOS(xfileraction_send_selected_directory((wimp_t)fileractiontaskhandle,srcdirbuffer));
							}
							CheckOS(xfileraction_send_selected_file((wimp_t)fileractiontaskhandle,namelist->info[0].name));
						}
					}
				}
			}
			namelist=(osgbpb_info_list *)((((int)namelist)+20+strlen(namelist->info[0].name)+4)&~3);
			numread--;
		}
		/*Do a bit of multitasking*/
		if (CHECKPOLL) {
			if (destdir && fileractiontaskhandle) StartFilerAction(destdirbuffer);
			fileractiontaskhandle=0;
			Desk_Icon_SetInteger(statuswin,status_COPIED,numfilescopied);
			Desk_Icon_SetInteger(statuswin,status_READ,numfilesread);
			if (!running) return;
		}
	} while (context!=osgbpb_NO_MORE);
	if (destdir && fileractiontaskhandle) StartFilerAction(destdirbuffer);
	fileractiontaskhandle=0;
	Desk_Icon_SetInteger(statuswin,status_COPIED,numfilescopied);
	Desk_Icon_SetInteger(statuswin,status_READ,numfilesread);
}

static void Backup(void)
{
	time_t currenttime;
	char *icontext;
	char *comma,*list;
	int i;
	char timebuf[BUFFER_SIZE];
	time_t timer;
	struct tm *now;

	Desk_Hourglass_On();
	running=Desk_TRUE;
	numfilesread=0;
	numfilescopied=0;
	Desk_Icon_SetInteger(statuswin,status_COPIED,numfilescopied);
	Desk_Icon_SetInteger(statuswin,status_READ,numfilesread);
	AJWLib_Msgs_SetText(statuswin,status_CANCEL,"Status.4:");

	time(&timer);
	now=localtime(&timer);

	traverseimages=Desk_Icon_GetSelect(mainwin,icon_IMAGES);
	faster=Desk_Icon_GetSelect(mainwin,icon_FASTER) ? fileraction_FASTER : 0;
	verbose=Desk_Icon_GetSelect(mainwin,icon_VERBOSE) ? fileraction_VERBOSE : 0;
	md5=Desk_Icon_GetSelect(mainwin,icon_MD5);

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_SRC);
	if (icontext[0]) {
		for (i=0;i<numsrcs;i++) free(srcdirs[i]);
		numsrcs=0;
		time(&timer);
		strftime(timebuf,BUFFER_SIZE,icontext,now);
		comma=list=timebuf;
		while (comma) {
			char *dir;
			char *buffer;
	
			comma=strchr(list,',');
			if (comma) *comma++='\0';
			dir=list;
			list=comma;
			buffer=Desk_DeskMem_Malloc(BUFFER_SIZE);
			if (xosfscontrol_canonicalise_path(dir,buffer,NULL,NULL,BUFFER_SIZE,&i)==NULL) {
				if (numsrcs<MAXSRCS) srcdirs[numsrcs++]=buffer;
			}
		}
	} else {
		Desk_Msgs_Report(1,"Error.NoSrc:Source directory cannot be left blank");
		running=Desk_FALSE;
		return;
	}

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_EXIST);
	if (icontext[0]) {
		strftime(timebuf,BUFFER_SIZE,icontext,now);
		oldlistfile=fopen(timebuf,"r");
		if (oldlistfile==NULL) {
			Desk_Msgs_Report(1,"Error.Open1:Can't open file");
			running=Desk_FALSE;
			return;
		}
	} else {
		oldlistfile=NULL;
	}

	if (destdir) free(destdir);
	icontext=Desk_Icon_GetTextPtr(mainwin,icon_DEST);
	if (icontext[0]) {
		strftime(timebuf,BUFFER_SIZE,icontext,now);
		destdir=Desk_strdup(timebuf);
	} else {
		destdir=NULL;
	}

	if (destdir) osfile_create_dir(destdir,0);

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_NEW);
	if (icontext[0]) {
		strftime(timebuf,BUFFER_SIZE,icontext,now);
		listfile=fopen(timebuf,"w");
		if (listfile==NULL) {
			Desk_Msgs_Report(1,"Error.Open2:Unable to open new list file");
			if (oldlistfile) fclose(oldlistfile);
			running=Desk_FALSE;
			return;
		}
	} else {
		listfile=NULL;
	}

	for (i=0;i<numexcludes;i++) free(excludes[i]);
	numexcludes=0;
	icontext=Desk_Icon_GetTextPtr(mainwin,icon_EXCLUDE);
	strftime(timebuf,BUFFER_SIZE,icontext,now);
	comma=list=timebuf;
	while (comma) {
		char *dir;
		char *buffer;

		comma=strchr(list,',');
		if (comma) *comma++='\0';
		dir=list;
		list=comma;
		buffer=Desk_DeskMem_Malloc(BUFFER_SIZE);
		if (xosfscontrol_canonicalise_path(dir,buffer,NULL,NULL,BUFFER_SIZE,&i)==NULL) {
			if (numexcludes<MAXEXCLUDES) excludes[numexcludes++]=buffer;
		}
	}


	Desk_Window_Hide(mainwin);
	Desk_Window_Show(statuswin,Desk_open_CENTERED);

	/*Read contents of old list file into hash table*/
	ReadFile();

	Desk_Icon_SetInteger(statuswin,status_COPIED,numfilescopied);
	Desk_Icon_SetInteger(statuswin,status_READ,numfilesread);

	/*Do the business*/
	for (i=0;i<numsrcs;i++) {
		srcdir=srcdirs[i];
		/*Print date and directory to the file (for human reference only)*/
		time(&currenttime);
		if (listfile) fprintf(listfile,"#%s#%s\n",ctime(&currenttime),srcdir);
		TraverseDir(NULL);
	}

	/*Concatenate old list file on end of new list file*/
	if (listfile && oldlistfile) {
		int count=0;
		AJWLib_Msgs_SetText(statuswin,status_DIR,"Status.2:");
		rewind(oldlistfile);
		while (!feof(oldlistfile)) {
			char buffer[BUFFER_SIZE];

			buffer[BUFFER_SIZE-1]='\0';
			if (fgets(buffer,BUFFER_SIZE-1,oldlistfile)) fputs(buffer,listfile);

			count++;
			if (count%200==0) MultiTask();
			if (!running) break;
		}
	}

	/*Tidy up*/
	if (hashtable) free(hashtable);
	hashtable = NULL;
	if (listfile) fclose(listfile);
	if (oldlistfile) fclose(oldlistfile);
	AJWLib_Msgs_SetText(statuswin,status_DIR,"Status.3:");
	AJWLib_Msgs_SetText(statuswin,status_CANCEL,"Status.5:");
	Desk_Hourglass_Off();
	if (running && startimmediatly) Desk_Event_CloseDown();
}

static Desk_bool ReceiveDrag(Desk_event_pollblock *block, void *ref)
{
	char *text;
	int len=0;
	Desk_bool replace;

	Desk_UNUSED(ref);
	switch (block->data.message.data.dataload.icon) {
		case icon_SRC:
		case icon_EXCLUDE:
			replace=Desk_FALSE;
			break;
		case icon_DEST:
		case icon_EXIST:
		case icon_NEW:
			replace=Desk_TRUE;
			break;
		default:
			replace=Desk_FALSE;
			return Desk_FALSE;
	}
	text=Desk_Icon_GetTextPtr(mainwin,block->data.message.data.dataload.icon);
	if (!replace) len=strlen(text);
	if (len+2+strlen(block->data.message.data.dataload.filename)>MAXICONLENGTH) {
		Desk_Msgs_Report(1,"Error.NoRoom:Not enough room in icon");
		return Desk_TRUE;
	}
	if (replace) {
		strcpy(text,block->data.message.data.dataload.filename);
	} else {
		if (text[0]) strcat(text,",");
		strcat(text,block->data.message.data.dataload.filename);
	}
	Desk_Icon_ForceRedraw(mainwin,block->data.message.data.dataload.icon);
	Desk_Icon_SetCaret(mainwin,block->data.message.data.dataload.icon);
	return Desk_TRUE;
}

static void SetIcons(void)
{
	Desk_Icon_SetText(mainwin,icon_SRC,defaults.src);
	Desk_Icon_SetText(mainwin,icon_DEST,defaults.dest);
	Desk_Icon_SetText(mainwin,icon_EXCLUDE,defaults.exclude);
	Desk_Icon_SetText(mainwin,icon_EXIST,defaults.existinglist);
	Desk_Icon_SetText(mainwin,icon_NEW,defaults.newlist);
	Desk_Icon_SetSelect(mainwin,icon_IMAGES,defaults.images);
	Desk_Icon_SetSelect(mainwin,icon_FASTER,defaults.faster);
	Desk_Icon_SetSelect(mainwin,icon_VERBOSE,defaults.verbose);
	Desk_Icon_SetSelect(mainwin,icon_MD5,defaults.md5);
	Desk_Window_Show(mainwin,Desk_open_CENTERED);
	Desk_Icon_SetCaret(mainwin,icon_SRC);
}

static Desk_bool IconBarClick(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.select) {
		if (running) {
			Desk_Window_BringToFront(statuswin);
		} else {
			SetIcons();
		}
		return Desk_TRUE;
	}
	return Desk_FALSE;
}

static Desk_bool CancelClick(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.menu) return Desk_FALSE;
	if (block->data.mouse.button.data.select) Desk_Window_Hide(mainwin);
	return Desk_TRUE;
}

static Desk_bool StatusCancelClick(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);

	if (block->data.mouse.button.data.menu) return Desk_FALSE;
	if (block->data.mouse.button.data.select) {
		Desk_Window_Hide(statuswin);
		Desk_Wimp_SetIconState(statuswin,status_SKIP,1<<23,1<<23); /*Delete icon*/
		if (fileractiontaskhandle) {
			Desk_message_block msgblk;

			msgblk.header.size=sizeof(Desk_message_header);
			msgblk.header.yourref=0;
			msgblk.header.action=Desk_message_QUIT;
			Desk_Wimp_SendMessage(Desk_event_USERMESSAGE,&msgblk,fileractiontaskhandle,-1);
		}
		running=Desk_FALSE;
	}
	return Desk_TRUE;
}

static Desk_bool OKClick(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.menu) return Desk_FALSE;
	if (block->data.mouse.button.data.select) Backup();
	return Desk_TRUE;
}

static Desk_bool IconDrag(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);
	if (!block->data.mouse.button.data.select) return Desk_FALSE;
	switch (block->data.mouse.icon) {
		case icon_SRCDRAG:
			dragicon=icon_SRC;
			break;
		case icon_DESTDRAG:
			dragicon=icon_DEST;
			break;
		case icon_EXCLUDEDRAG:
			dragicon=icon_EXCLUDE;
			break;
		case icon_NEWDRAG:
			dragicon=icon_NEW;
			break;
		default:
			return Desk_FALSE;
	}
	Desk_Icon_StartSolidDrag(mainwin,block->data.mouse.icon);
	return Desk_TRUE;
}

static Desk_bool DataSaveAckHandler(Desk_event_pollblock *block, void *ref)
{
	char *filename,*leafname;
	int len;

	Desk_UNUSED(ref);
	filename=block->data.message.data.datasaveack.filename;
	len=strlen(filename);
	if (len>5 && dragicon!=icon_NEW) {
		leafname=filename+len-5;
		if (Desk_stricmp(leafname,".List")==0) filename[len-5]='\0';
	}
	Desk_Icon_SetText(mainwin,dragicon,filename);
	Desk_Icon_SetCaret(mainwin,dragicon);
	return Desk_TRUE;
}

static Desk_bool DragHandler(Desk_event_pollblock *block, void *ref)
{
	Desk_mouse_block ptrblk;
	Desk_message_block msgblk;
	char *leafname;

	Desk_UNUSED(block);
	Desk_UNUSED(ref);
	Desk_Wimp_GetPointerInfo(&ptrblk);
	if (dragicon==icon_NEW) leafname=Desk_Str_LeafName(Desk_Icon_GetTextPtr(mainwin,dragicon)); else leafname="List";
	if (leafname[0]) strcpy(msgblk.data.datasave.leafname,leafname); else strcpy(msgblk.data.datasave.leafname,"List");
	msgblk.header.size=(sizeof(Desk_message_header)+28+strlen(msgblk.data.datasave.leafname)) & ~3;
	msgblk.header.yourref=0;
	msgblk.header.action=Desk_message_DATASAVE;
	msgblk.data.datasave.window=ptrblk.window;
	msgblk.data.datasave.icon=ptrblk.icon;
	msgblk.data.datasave.pos=ptrblk.pos;
	msgblk.data.datasave.estsize=1;
	msgblk.data.datasave.filetype=0x1000;
	Desk_Wimp_SendMessage(Desk_event_USERMESSAGE,&msgblk,ptrblk.window,ptrblk.icon);
	return Desk_TRUE;
}

static void IconBarMenuClick(int entry, void *ref)
{
	Desk_UNUSED(ref);
	switch (entry) {
		case iconbarmenu_HELP:
			system("Filer_Run <" DIRPREFIX "$Dir>.!Help");
			break;
		case iconbarmenu_QUIT:
			Desk_Event_CloseDown();
			break;
	}
}

#define FindEndOfLine(x) {\
	while (*x!='\0' && *x!='\n') x++;\
	if (*x=='\0') return;\
	*(x++)='\0';\
}

static void LoadDefaults(char *filename)
{
	char *file;

	defaults.src="";
	defaults.dest="";
	defaults.exclude="";
	defaults.existinglist="";
	defaults.newlist="";
	defaults.images=Desk_FALSE;
	defaults.faster=Desk_FALSE;
	defaults.verbose=Desk_TRUE;
	defaults.md5=Desk_TRUE;
	if (Desk_File_Exists(filename)) {
		if ((file=Desk_File_AllocLoad0(filename))!=NULL) {
			defaults.src=file;
			FindEndOfLine(file);
			defaults.dest=file;
			FindEndOfLine(file);
			defaults.exclude=file;
			FindEndOfLine(file);
			defaults.existinglist=file;
			FindEndOfLine(file);
			defaults.newlist=file;
			FindEndOfLine(file);
			defaults.images=(Desk_bool)strtol(file,&file,10);
			defaults.faster=(Desk_bool)strtol(file,&file,10);
			defaults.verbose=(Desk_bool)strtol(file,&file,10);
			defaults.md5=(Desk_bool)strtol(file,&file,10);
		}
	}
}

static Desk_bool SaveDefaults(Desk_event_pollblock *block, void *ref)
{
	FILE *file;
	char *filename;

	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.menu) return Desk_FALSE;
	/* This is a small memory leak... */
	defaults.src=Desk_strdup(Desk_Icon_GetTextPtr(mainwin,icon_SRC));
	defaults.dest=Desk_strdup(Desk_Icon_GetTextPtr(mainwin,icon_DEST));
	defaults.exclude=Desk_strdup(Desk_Icon_GetTextPtr(mainwin,icon_EXCLUDE));
	defaults.existinglist=Desk_strdup(Desk_Icon_GetTextPtr(mainwin,icon_EXIST));
	defaults.newlist=Desk_strdup(Desk_Icon_GetTextPtr(mainwin,icon_NEW));
	defaults.images=Desk_Icon_GetSelect(mainwin,icon_IMAGES);
	defaults.faster=Desk_Icon_GetSelect(mainwin,icon_FASTER);
	defaults.verbose=Desk_Icon_GetSelect(mainwin,icon_VERBOSE);
	defaults.md5=Desk_Icon_GetSelect(mainwin,icon_MD5);
	if (getenv("Choices$Write")) {
		osfile_create_dir("<Choices$Write>.YABU",1);
		filename="<Choices$Write>.YABU.Defaults";
	} else {
		filename="<YABU$Dir>.Defaults";
	}
	file=AJWLib_File_fopen(filename,"w");
	fprintf(file,"%s\n",defaults.src);
	fprintf(file,"%s\n",defaults.dest);
	fprintf(file,"%s\n",defaults.exclude);
	fprintf(file,"%s\n",defaults.existinglist);
	fprintf(file,"%s\n",defaults.newlist);
	fprintf(file,"%d\n",defaults.images);
	fprintf(file,"%d\n",defaults.faster);
	fprintf(file,"%d\n",defaults.verbose);
	fprintf(file,"%d\n",defaults.md5);
	fclose(file);

	return Desk_TRUE;
}

int main(int argc, char *argv[])
{
#ifdef MemCheck_MEMCHECK
	MemCheck_Init();
	MemCheck_RegisterArgs(argc,argv);
	MemCheck_InterceptSCLStringFunctions();
	MemCheck_SetStoreMallocFunctions(1);
	MemCheck_SetAutoOutputBlocksInfo(0);
#endif

#ifdef HierProf_PROFILE
	HierProf_ProfileAllFunctions();
#endif

	Desk_Error2_Init_JumpSig();
	signal(SIGABRT,SIG_DFL);

	Desk_Error2_Try {
		Desk_Hourglass_On();
#ifdef MemCheck_MEMCHECK
		MemCheck_SetChecking(0,0);
#endif
		Desk_Resource_Initialise(DIRPREFIX);
#ifdef MemCheck_MEMCHECK
		MemCheck_SetChecking(1,1);
#endif
		Desk_Msgs_LoadFile("Messages");
		Desk_Event_Initialise(taskname=AJWLib_Msgs_Lookup("Task.Name:"));
		errbad=AJWLib_Msgs_Lookup("Error.Bad:%s Click Ok to continue, Cancel to quit.");
		Desk_EventMsg_Initialise();
		Desk_Screen_CacheModeInfo();
		Desk_Template_Initialise();
		Desk_EventMsg_Claim(Desk_message_MODECHANGE,Desk_event_ANY,Desk_Handler_ModeChange,NULL);
		Desk_Event_Claim(Desk_event_CLOSE,Desk_event_ANY,Desk_event_ANY,Desk_Handler_CloseWindow,NULL);
		Desk_Event_Claim(Desk_event_OPEN,Desk_event_ANY,Desk_event_ANY,Desk_Handler_OpenWindow,NULL);
		Desk_Event_Claim(Desk_event_KEY,Desk_event_ANY,Desk_event_ANY,Desk_Handler_Key,NULL);
		Desk_Event_Claim(Desk_event_REDRAW,Desk_event_ANY,Desk_event_ANY,Desk_Handler_HatchRedraw,NULL);
		Desk_Icon_BarIcon(AJWLib_Msgs_TempLookup("Task.Icon:"),Desk_iconbar_RIGHT);
		Desk_Template_LoadFile("Templates");
		proginfowin=AJWLib_Window_CreateInfoWindowFromMsgs("Task.Name:","Task.Purpose:",AUTHOR,VERSION);
		mainwin=Desk_Window_Create("main",Desk_template_TITLEMIN);
		statuswin=Desk_Window_Create("status",Desk_template_TITLEMIN);
		iconbarmenu=AJWLib_Menu_CreateFromMsgs("Title.IconBar:","Menu.IconBar:Info,Quit",IconBarMenuClick,NULL);
		Desk_Menu_AddSubMenu(iconbarmenu,iconbarmenu_INFO,(Desk_menu_ptr)proginfowin);
		AJWLib_Menu_Attach(Desk_window_ICONBAR,Desk_event_ANY,iconbarmenu,Desk_button_MENU);
		Desk_Event_Claim(Desk_event_CLICK,Desk_window_ICONBAR,Desk_event_ANY,IconBarClick,NULL);
		Desk_EventMsg_Claim(Desk_message_DATALOAD,mainwin,ReceiveDrag,NULL);
		Desk_EventMsg_Claim(Desk_message_DATASAVEACK,Desk_event_ANY,DataSaveAckHandler,NULL);
		Desk_EventMsg_Claim(Desk_message_TASKCLOSEDOWN,Desk_event_ANY,TaskCloseDownMsg,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_SRCDRAG,IconDrag,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_DESTDRAG,IconDrag,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_EXCLUDEDRAG,IconDrag,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_NEWDRAG,IconDrag,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_OK,OKClick,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_CANCEL,CancelClick,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_SAVEDEFAULT,SaveDefaults,NULL);
		Desk_Event_Claim(Desk_event_CLICK,statuswin,status_CANCEL,StatusCancelClick,NULL);
		Desk_Event_Claim(Desk_event_CLICK,statuswin,status_SKIP,SkipClick,NULL);
		Desk_Event_Claim(Desk_event_USERDRAG,Desk_event_ANY,Desk_event_ANY,DragHandler,NULL);
	} Desk_Error2_Catch {
		Desk_Hourglass_Off();
		AJWLib_Error2_Report("Fatal error while initialising (%s)");
		return EXIT_FAILURE;
	} Desk_Error2_EndCatch
	Desk_Hourglass_Off();
	Desk_Error2_Try {
		if (argc==2) {
			startimmediatly=Desk_TRUE;
			LoadDefaults(argv[1]);
			SetIcons();
			Backup();
		} else {
			char *filename;
			if (getenv("Choices$Path")) {
				filename="Choices:YABU.Defaults";
			} else {
				filename="<YABU$Dir>.Defaults";
			}
			LoadDefaults(filename);
		}
	} Desk_Error2_Catch {
		Desk_os_error errblk={1,""};
		sprintf(errblk.errmess,errbad,AJWLib_Error2_Describe(&Desk_Error2_globalblock));
		if (Desk_Wimp_ReportErrorR(&errblk,3,taskname)==Desk_wimp_reporterror_button_CANCEL) return EXIT_FAILURE;
	} Desk_Error2_EndCatch

	while (Desk_TRUE) {
		Desk_Error2_Try {
			Desk_Event_Poll();
		} Desk_Error2_Catch {
			Desk_os_error errblk={1,""};
			sprintf(errblk.errmess,errbad,AJWLib_Error2_Describe(&Desk_Error2_globalblock));
			if (Desk_Wimp_ReportErrorR(&errblk,3,taskname)==Desk_wimp_reporterror_button_CANCEL) return EXIT_FAILURE;
		} Desk_Error2_EndCatch
	}
	return EXIT_SUCCESS;
}


