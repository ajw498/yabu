/*
	Backup
	� Alex Waugh 2000

	$Id: Main.c,v 1.8 2000-11-13 11:53:32 AJW Exp $
*/

#include "MemCheck:MemCheck.h"
#include "HierProf:HierProf.h"

#include "OSLib:osgbpb.h"
#include "OSLib:osfscontrol.h"
#include "OSLib:fileraction.h"

#include "Desk.Window.h"
#include "Desk.Error2.h"
#include "Desk.Event.h"
#include "Desk.EventMsg.h"
#include "Desk.Handler.h"
#include "Desk.Hourglass.h"
#include "Desk.Icon.h"
#include "Desk.Menu.h"
#include "Desk.Msgs.h"
#include "Desk.Filing.h"
#include "Desk.DeskMem.h"
#include "Desk.Resource.h"
#include "Desk.Screen.h"
#include "Desk.Template.h"
#include "Desk.Str.h"
#include "Desk.File.h"
#include "Desk.Sprite.h"

#include "AJWLib.Window.h"
#include "AJWLib.Menu.h"
#include "AJWLib.Msgs.h"
#include "AJWLib.Error2.h"

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <time.h>
#include <string.h>

#define DIRPREFIX "Backup"
#define VERSION "1.00"
#define AUTHOR "� Alex Waugh 2000"

#define iconbarmenu_INFO 0
#define iconbarmenu_QUIT 1

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

#define status_DIR 0
#define status_READ 2
#define status_COPIED 4
#define status_SKIP 6
#define status_CANCEL 7

#define MAXICONLENGTH 256
#define MAXEXCLUDES 256
#define BUFFER_SIZE 1024
#define HASHTABLE_INCREMENT 10240

#define CheckOS(x) Desk_Error2_CheckOS((Desk_os_error *)x)

#define MultiTask() {\
 	Desk_Event_mask.data.null=0;\
	Desk_Hourglass_Off();\
	Desk_Event_Poll();\
	Desk_Hourglass_On();\
	Desk_Event_mask.data.null=1;\
}


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
static Desk_bool traverseimages,running=Desk_FALSE;
static int faster=0;
static Desk_icon_handle dragicon;

static Desk_bool keeppolling=Desk_FALSE;
static Desk_task_handle fileractiontaskhandle=0;
static int numfilesread,numfilescopied;
static int numexcludes=0;
static char *excludes[MAXEXCLUDES];

static Desk_window_handle proginfowin,mainwin,statuswin;
static Desk_menu_ptr iconbarmenu;
static char *taskname=NULL,*errbad=NULL;


static int GenerateKey(char *filename, int size)
/*generate a hash table key for given filename*/
{
	int len, i, key = 0;
	
	len = strlen(filename);
	for (i=0; i<len; i++) key += i*filename[i];
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
			if (sscanf(linebuffer,"%X\t%X\t%u\t%s\n",&load_addr,&exec_addr,&size,namebuffer)==4) {
				entry=Desk_DeskMem_Malloc(sizeof(struct hashentry));
				entry->load_addr=load_addr;
				entry->exec_addr=exec_addr;
				entry->size=size;
				entry->filename=Desk_DeskMem_Malloc(strlen(namebuffer)+1);
				strcpy(entry->filename,namebuffer);
				/*Put details in hash table*/
				InsertEntry(entry);

				count++;
				if (count%200==0) {
					Desk_Icon_SetInteger(statuswin,status_READ,count);
					MultiTask();
					if (!running) return;
				}
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

static Desk_bool TaskCloseDownMsg(Desk_event_pollblock *block,void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.message.header.sender==fileractiontaskhandle) keeppolling=Desk_FALSE;
	return Desk_TRUE;
}

static void StartFilerAction(char *dest)
{
	CheckOS(xfileractionsendstartoperation_copy((wimp_t)fileractiontaskhandle,(fileraction_VERBOSE | fileraction_FORCE | faster),dest,strlen(dest)+1));

	/*Poll the wimp, and let Filer_Action do it's thing*/
	keeppolling=Desk_TRUE;
	while (keeppolling) {
		Desk_Hourglass_Off();
		Desk_Event_Poll();
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
	osgbpb_info_list *namelist=(osgbpb_info_list *)namebuffer;

	/*Do a bit of multitasking*/
	MultiTask();
	if (!running) return;

	/*Get full name of directory we are copying from and to*/
	if (dir) sprintf(srcdirbuffer,"%s.%s",srcdir,dir); else sprintf(srcdirbuffer,"%s",srcdir);
	if (destdir) {
		if (dir) sprintf(destdirbuffer,"%s.%s",destdir,dir); else sprintf(destdirbuffer,"%s",destdir);
	}

	Desk_Icon_SetText(statuswin,status_DIR,srcdirbuffer);

	/*Scan thought the directory contents*/
	do {
		os_error *err;
		err=xosgbpb_dir_entries_info(srcdirbuffer,namelist,1,context,BUFFER_SIZE,NULL,&numread,&context);
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
		if (numread!=0) {
			char buffer[BUFFER_SIZE];
			char canonical[BUFFER_SIZE];
			Desk_bool exclude=Desk_FALSE;
			int i;

			if (dir) sprintf(buffer,"%s.%s.%s",srcdirbuffer,dir,namelist->info[0].name); else sprintf(buffer,"%s.%s",srcdirbuffer,namelist->info[0].name);
			if (xosfscontrol_canonicalise_path(buffer,canonical,NULL,NULL,BUFFER_SIZE,&i)) strcpy(canonical,buffer);
			for (i=0;i<numexcludes;i++) {
				if (strcmp(canonical,excludes[i])==0) {
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
	
					numfilesread++;
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

	Desk_Hourglass_On();
	running=Desk_TRUE;
	numfilesread=0;
	numfilescopied=0;
	Desk_Icon_SetInteger(statuswin,status_COPIED,numfilescopied);
	Desk_Icon_SetInteger(statuswin,status_READ,numfilesread);
	AJWLib_Msgs_SetText(statuswin,status_CANCEL,"Status.4:");

	traverseimages=Desk_Icon_GetSelect(mainwin,icon_IMAGES);
	faster=Desk_Icon_GetSelect(mainwin,icon_FASTER) ? fileraction_FASTER : 0;

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_SRC);
	if (icontext[0]) {
		srcdir=icontext;
	} else {
		Desk_Msgs_Report(1,"Error.NoSrc:Source directory cannot be left blank");
		running=Desk_FALSE;
		return;
	}

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_EXIST);
	if (icontext[0]) {
		oldlistfile=fopen(icontext,"r");
		if (oldlistfile==NULL) {
			Desk_Msgs_Report(1,"Error.Open1:Can't open file");
			running=Desk_FALSE;
			return;
		}
	} else {
		oldlistfile=NULL;
	}

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_DEST);
	if (icontext[0]) destdir=icontext; else destdir=NULL;

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_NEW);
	if (icontext[0]) {
		listfile=fopen(icontext,"w");
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
	comma=list=Desk_Icon_GetTextPtr(mainwin,icon_EXCLUDE);
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

	/*Print date and directory to the file (for human reference only)*/
	time(&currenttime);
	if (listfile) fprintf(listfile,"#%s#%s\n",ctime(&currenttime),srcdir);

	/*Do the business*/
	TraverseDir(NULL);

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
	if (listfile) fclose(listfile);
	if (oldlistfile) fclose(oldlistfile);
	AJWLib_Msgs_SetText(statuswin,status_DIR,"Status.3:");
	AJWLib_Msgs_SetText(statuswin,status_CANCEL,"Status.5:");
	Desk_Hourglass_Off();
}

static Desk_bool ReceiveDrag(Desk_event_pollblock *block, void *ref)
{
	char *text;
	int len=0;
	Desk_bool replace;

	Desk_UNUSED(ref);
	switch (block->data.message.data.dataload.icon) {
		case icon_EXCLUDE:
			replace=Desk_FALSE;
			break;
		case icon_SRC:
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

static Desk_bool IconBarClick(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.select) {
		if (running) {
			Desk_Window_BringToFront(statuswin);
		} else {
			Desk_Icon_SetText(mainwin,icon_SRC,"");
			Desk_Icon_SetText(mainwin,icon_DEST,"");
			Desk_Icon_SetText(mainwin,icon_EXCLUDE,"");
			Desk_Icon_SetText(mainwin,icon_EXIST,"");
			Desk_Icon_SetText(mainwin,icon_NEW,"");
			Desk_Window_Show(mainwin,Desk_open_CENTERED);
			Desk_Icon_SetCaret(mainwin,icon_SRC);
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
	if (entry==iconbarmenu_QUIT) Desk_Event_CloseDown();
}

int main(void)
{
	MemCheck_Init();
/*	MemCheck_RegisterArgs(argc,argv);*/
	MemCheck_InterceptSCLStringFunctions();
	MemCheck_SetStoreMallocFunctions(1);
	MemCheck_SetAutoOutputBlocksInfo(0);

	HierProf_ProfileAllFunctions();

	Desk_Error2_Init_JumpSig();
	signal(SIGABRT,SIG_DFL);

	Desk_Error2_Try {
		Desk_Hourglass_On();
		MemCheck_SetChecking(0,0);
		Desk_Resource_Initialise(DIRPREFIX);
		MemCheck_SetChecking(1,1);
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
		Desk_Event_Claim(Desk_event_CLICK,statuswin,status_CANCEL,StatusCancelClick,NULL);
		Desk_Event_Claim(Desk_event_CLICK,statuswin,status_SKIP,SkipClick,NULL);
		Desk_Event_Claim(Desk_event_USERDRAG,Desk_event_ANY,Desk_event_ANY,DragHandler,NULL);
	} Desk_Error2_Catch {
		Desk_Hourglass_Off();
		AJWLib_Error2_Report("Fatal error while initialising (%s)");
		return EXIT_FAILURE;
	} Desk_Error2_EndCatch


	/*Sort out command line arguments?*/

	Desk_Hourglass_Off();
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


