/*
	Backup
	© Alex Waugh 2000

	$Id: Main.c,v 1.3 2000-11-09 23:30:24 AJW Exp $
*/

#include "MemCheck:MemCheck.h"

#include "OSLib:osgbpb.h"
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
#define AUTHOR "© Alex Waugh 2000"

#define iconbarmenu_INFO 0
#define iconbarmenu_QUIT 1

#define icon_OK 16
#define icon_CANCEL 15
#define icon_IMAGES 5
#define icon_SRC 6
#define icon_SRCDRAG 11
#define icon_DEST 7
#define icon_DESTDRAG 12
#define icon_EXCLUDE 8
#define icon_EXCLUDEDRAG 13
#define icon_EXIST 9
#define icon_NEW 10
#define icon_NEWDRAG 14

#define MAXICONLENGTH 256

#define BUFFER_SIZE 1024
#define HASHTABLE_INCREMENT 1024

#define CheckOS(x) Desk_Error2_CheckOS((Desk_os_error *)x)


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

static Desk_bool keeppolling=Desk_FALSE;
static Desk_task_handle fileractiontaskhandle=0;

static Desk_window_handle proginfowin,mainwin;
static Desk_menu_ptr iconbarmenu;
static char *taskname=NULL,*errbad=NULL;


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
	hashtable=Desk_DeskMem_Malloc(hashtablesize*sizeof(struct hashentry *));
	for (i=0; i<hashtablesize; i++) hashtable[i] = NULL;
	if (oldlistfile) {
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
	CheckOS(xfileractionsendstartoperation_copy((wimp_t)fileractiontaskhandle,(fileraction_VERBOSE | fileraction_FORCE/* | fileraction_FASTER*/),dest,strlen(dest)+1));

	/*Poll the wimp, and let Filer_Action do it's thing*/
	Desk_Hourglass_Off();
	keeppolling=Desk_TRUE;
	while (keeppolling) Desk_Event_Poll();
	Desk_Hourglass_On();
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
	Desk_Event_mask.data.null=0;
	Desk_Hourglass_Off();
	Desk_Event_Poll();
	Desk_Hourglass_On();
	Desk_Event_mask.data.null=1;

	/*Get full name of directory we are copying from and to*/
	if (dir) sprintf(srcdirbuffer,"%s.%s",srcdir,dir); else sprintf(srcdirbuffer,"%s",srcdir);
	if (destdir) {
		if (dir) sprintf(destdirbuffer,"%s.%s",destdir,dir); else sprintf(destdirbuffer,"%s",destdir);
	}

	/*Scan thought the directory contents*/
	do {
		CheckOS(xosgbpb_dir_entries_info(srcdirbuffer,namelist,1,context,BUFFER_SIZE,NULL,&numread,&context));
		if (numread!=0) {
			char buffer[BUFFER_SIZE];

			if (dir) sprintf(buffer,"%s.%s",dir,namelist->info[0].name); else sprintf(buffer,"%s",namelist->info[0].name);
			if (namelist->info[0].obj_type==fileswitch_IS_DIR || (config.traverseimages && namelist->info[0].obj_type==fileswitch_IS_IMAGE)) {
				if (destdir && fileractiontaskhandle) StartFilerAction(destdirbuffer);
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
							Desk_Wimp_StartTask3("Filer_Action",&fileractiontaskhandle);
							CheckOS(xfileraction_send_selected_directory((wimp_t)fileractiontaskhandle,srcdirbuffer));
						}
						CheckOS(xfileraction_send_selected_file((wimp_t)fileractiontaskhandle,namelist->info[0].name));
					}
				}
			}
		}
	} while (context!=osgbpb_NO_MORE);
	if (destdir && fileractiontaskhandle) StartFilerAction(destdirbuffer);
	fileractiontaskhandle=0;
}

static void Backup(void)
{
	time_t currenttime;
	char *icontext;

	Desk_Hourglass_On();
	icontext=Desk_Icon_GetTextPtr(mainwin,icon_EXIST);
	if (icontext[0]) {
		oldlistfile=fopen(icontext,"r");
		if (oldlistfile==NULL) AJWLib_Error2_HandleMsgs("Error.Open1:Can't open file");
	} else {
		oldlistfile=NULL;
	}

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_SRC);
	if (icontext[0]) {
		srcdir=icontext;
	} else {
		AJWLib_Error2_HandleMsgs("Error.NoSrc:Source directory cannot be none");
	}

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_DEST);
	if (icontext[0]) destdir=icontext; else destdir=NULL;

	icontext=Desk_Icon_GetTextPtr(mainwin,icon_NEW);
	if (icontext[0]) {
		listfile=fopen(icontext,"w");
		if (listfile==NULL) AJWLib_Error2_HandleMsgs("Error.Open2:Unable to open new list file");
	} else {
		listfile=NULL;
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
	Desk_Hourglass_Off();
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
		Desk_Error_Report(1,"Not enough room in icon"); /*msgs*/
		return Desk_TRUE;
	}
	if (replace) {
		strcpy(text,block->data.message.data.dataload.filename);
	} else {
		if (text[0]) strcat(text,",");
		strcat(text,block->data.message.data.dataload.filename);
	}
	Desk_Icon_ForceRedraw(mainwin,block->data.message.data.dataload.icon);
	return Desk_TRUE;
}

static Desk_bool IconBarClick(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.select) {
		Desk_Window_Show(mainwin,Desk_open_CENTERED);
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

static Desk_bool OKClick(Desk_event_pollblock *block, void *ref)
{
	Desk_UNUSED(ref);
	if (block->data.mouse.button.data.menu) return Desk_FALSE;
	if (block->data.mouse.button.data.select) Desk_Window_Hide(mainwin);
	Backup();
	return Desk_TRUE;
}

static void IconBarMenuClick(int entry, void *ref)
{
	Desk_UNUSED(ref);
	if (entry==iconbarmenu_QUIT) Desk_Event_CloseDown();
}

int main(int argc, char *argv[])
{
	MemCheck_Init();
	MemCheck_RegisterArgs(argc,argv);
	MemCheck_InterceptSCLStringFunctions();
	MemCheck_SetStoreMallocFunctions(1);
	MemCheck_SetAutoOutputBlocksInfo(0);

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
		iconbarmenu=AJWLib_Menu_CreateFromMsgs("Title.IconBar:","Menu.IconBar:Info,Quit",IconBarMenuClick,NULL);
		Desk_Menu_AddSubMenu(iconbarmenu,iconbarmenu_INFO,(Desk_menu_ptr)proginfowin);
		AJWLib_Menu_Attach(Desk_window_ICONBAR,Desk_event_ANY,iconbarmenu,Desk_button_MENU);
		Desk_Event_Claim(Desk_event_CLICK,Desk_window_ICONBAR,Desk_event_ANY,IconBarClick,NULL);
		Desk_EventMsg_Claim(Desk_message_DATALOAD,mainwin,ReceiveDrag,NULL);
		Desk_EventMsg_Claim(Desk_message_TASKCLOSEDOWN,Desk_event_ANY,TaskCloseDownMsg,NULL);
/*		Desk_Event_Claim(Desk_event_CLICK,mainwin,Desk_event_ANY,IconClick,NULL);*/
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_OK,OKClick,NULL);
		Desk_Event_Claim(Desk_event_CLICK,mainwin,icon_CANCEL,CancelClick,NULL);
	} Desk_Error2_Catch {
		Desk_Hourglass_Off();
		AJWLib_Error2_Report("Fatal error while initialising (%s)");
		return EXIT_FAILURE;
	} Desk_Error2_EndCatch


	/*Sort out command line arguments*/
/*	if (argc!=5) Error("Usage: "TASKNAME" srcdir destdir oldlist newlist");
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
	}*/

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


