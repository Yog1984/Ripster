"""Ripster - Windows audio CD ripper. Python 3.11+, Windows only."""
import ctypes, ctypes.wintypes as wt
import json, os, re, struct, subprocess, sys, threading, time, urllib.request, urllib.parse, wave
from pathlib import Path
import winsound
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP='Ripster'; SECTOR=2352; FRAMES=75
IOCTL_CDROM_READ_TOC=0x00024000
IOCTL_CDROM_RAW_READ=0x0002403E
GENERIC_READ=0x80000000; FILE_SHARE_READ=1; FILE_SHARE_WRITE=2; OPEN_EXISTING=3
INVALID_HANDLE_VALUE=ctypes.c_void_p(-1).value
kernel=ctypes.windll.kernel32 if os.name=='nt' else None
if kernel:
    kernel.CreateFileW.argtypes=[wt.LPCWSTR,wt.DWORD,wt.DWORD,wt.LPVOID,wt.DWORD,wt.DWORD,wt.HANDLE]
    kernel.CreateFileW.restype=wt.HANDLE
    kernel.DeviceIoControl.argtypes=[wt.HANDLE,wt.DWORD,wt.LPVOID,wt.DWORD,wt.LPVOID,wt.DWORD,ctypes.POINTER(wt.DWORD),wt.LPVOID]
    kernel.DeviceIoControl.restype=wt.BOOL
    kernel.CloseHandle.argtypes=[wt.HANDLE]

def clean(s):
    s=re.sub(r'[<>:"/\\|?*\x00-\x1f]','_',s).strip(' .')
    return s[:120] or 'Inconnu'

def drive_letters():
    if os.name!='nt': return []
    return [f'{chr(c)}:' for c in range(65,91) if ctypes.windll.kernel32.GetDriveTypeW(f'{chr(c)}:\\')==5]

class CD:
    def __init__(self,letter):
        self.h=kernel.CreateFileW('\\\\.\\'+letter,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE,None,OPEN_EXISTING,0,None)
        if self.h==INVALID_HANDLE_VALUE: raise OSError('Impossible d’ouvrir le lecteur CD. Vérifiez le disque et les permissions.')
        try: self.toc=self.read_toc()
        except: self.close(); raise
    def ioctl(self,code,inp,out):
        done=wt.DWORD()
        ok=kernel.DeviceIoControl(self.h,code,inp,ctypes.sizeof(inp) if inp is not None else 0,out,ctypes.sizeof(out),ctypes.byref(done),None)
        if not ok: raise ctypes.WinError()
        return done.value
    def read_toc(self):
        b=ctypes.create_string_buffer(804)
        self.ioctl(IOCTL_CDROM_READ_TOC,None,b)
        raw=b.raw; first=raw[2]; last=raw[3]
        if first<1 or last<first or last>99: raise ValueError('Table des pistes CD invalide')
        tracks=[]
        for n in range(last-first+2):
            e=raw[4+n*8:12+n*8]
            if len(e)<8: raise ValueError('TOC incomplet')
            # Address[0] reserved, Address[1:4] is M:S:F, TOC format MSF
            lba=(e[5]*60+e[6])*75+e[7]-150
            tracks.append({'num':first+n,'lba':lba,'control':e[1]>>4})
        for i in range(len(tracks)-1): tracks[i]['end']=tracks[i+1]['lba']
        return tracks[:-1]
    def read_sectors(self,lba,count):
        # RAW_READ_INFO: LARGE_INTEGER DiskOffset, ULONG SectorCount, TRACK_MODE_TYPE TrackMode (CDDA=2)
        inp=ctypes.create_string_buffer(struct.pack('<qII',lba*2048,count,2))
        out=ctypes.create_string_buffer(count*SECTOR)
        n=self.ioctl(IOCTL_CDROM_RAW_READ,inp,out)
        if n!=count*SECTOR: raise IOError('Lecture CD incomplète')
        return out.raw
    def close(self):
        if self.h!=INVALID_HANDLE_VALUE: kernel.CloseHandle(self.h); self.h=INVALID_HANDLE_VALUE

def discid(toc):
    # MusicBrainz disc ID: SHA-1 of first,last,leadout,99 offsets in hex, base64 URL-safe.
    import hashlib,base64
    first=toc[0]['num']; last=toc[-1]['num']; lead=toc[-1]['end']+150
    offsets={t['num']:t['lba']+150 for t in toc}
    data=f'{first:02X}{last:02X}{lead:08X}'+''.join(f'{offsets.get(i,0):08X}' for i in range(1,100))
    return base64.b64encode(hashlib.sha1(data.encode('ascii')).digest()).decode().replace('+','.').replace('/','_').replace('=','-')

def lookup(toc):
    id=discid(toc)
    url=f'https://musicbrainz.org/ws/2/discid/{id}?inc=recordings+artists&fmt=json'
    req=urllib.request.Request(url,headers={'User-Agent':'Ripster/1.0 (personal desktop ripper)','Accept':'application/json'})
    with urllib.request.urlopen(req,timeout=12) as r: data=json.load(r)
    releases=data.get('releases',[])
    if not releases: raise ValueError('Album non trouvé sur MusicBrainz.')
    release=releases[0]; media=release.get('media',[])
    medium=next((m for m in media if any(d.get('id')==id for d in m.get('discs',[]))),media[0] if media else {})
    names=[t.get('title',f'Piste {i+1:02}') for i,t in enumerate(medium.get('tracks',[]))]
    artist=''.join(a.get('name','')+a.get('joinphrase','') for a in release.get('artist-credit',[]) if isinstance(a,dict)) or 'Artiste inconnu'
    return artist,release.get('title','Album inconnu'),release.get('date','')[:4],names

def ffmpeg_path():
    base=Path(getattr(sys,'_MEIPASS',Path(__file__).parent))
    p=base/'ffmpeg.exe'
    return str(p) if p.exists() else None

class App:
    def __init__(self,root):
        self.root=root;root.title('Ripster — Extracteur de CD Audio');root.geometry('1160x760');root.minsize(930,650)
        self.bg='#091326';self.panel='#10213b';self.fg='#eff5ff';self.accent='#a449fa';self.cyan='#26d7ee'
        root.configure(bg=self.bg);self.busy=False;self.tracks=[];self.entries=[];self.cancel=False
        self.artist=tk.StringVar();self.album=tk.StringVar();self.year=tk.StringVar();self.genre=tk.StringVar()
        self.want_wav=tk.BooleanVar(value=False);self.want_mp3=tk.BooleanVar(value=True);self.want_flac=tk.BooleanVar(value=False);self.bitrate=tk.StringVar(value='320');self.folder=tk.StringVar(value=str(Path.home()/'Music'))
        self.drive=tk.StringVar();self.status=tk.StringVar(value='Prêt. Insérez un CD audio.');self.autofetch=tk.BooleanVar(value=True)
        self.sound_success=tk.BooleanVar(value=True);self.sound_error=tk.BooleanVar(value=True);self.sound_disc=tk.BooleanVar(value=True)
        self.make_ui();self.refresh()
    def label(self,parent,text,size=11,color=None,bold=False):
        return tk.Label(parent,text=text,bg=parent.cget('bg'),fg=color or self.fg,font=('Segoe UI',size,'bold' if bold else 'normal'))
    def entry(self,parent,var,width=35):
        e=tk.Entry(parent,textvariable=var,bg='#1b3050',fg='white',insertbackground='white',relief='flat',font=('Segoe UI',11),width=width)
        return e
    def btn(self,parent,text,cmd,color=None):
        return tk.Button(parent,text=text,command=cmd,bg=color or '#234569',fg='white',activebackground=self.accent,activeforeground='white',relief='flat',font=('Segoe UI',10,'bold'),padx=12,pady=9,cursor='hand2')
    def panel_box(self,parent,title):
        frame=tk.Frame(parent,bg=self.panel,highlightbackground='#315079',highlightthickness=1,padx=13,pady=12)
        self.label(frame,title,13,self.cyan,True).pack(anchor='w',pady=(0,10))
        return frame
    def make_ui(self):
        head=tk.Frame(self.root,bg='#121c3e',padx=22,pady=16);head.pack(fill='x')
        self.label(head,'💿  RIPSTER',29,'#f1f3ff',True).pack(side='left')
        self.label(head,'    EXTRACTION AUDIO  •  WAV / FLAC / MP3',12,self.cyan,True).pack(side='left',padx=14)
        self.label(head,'♪  ▂▅▇▃▆▂▇▅▃▆',19,'#ef45a3',True).pack(side='right')
        top=tk.Frame(self.root,bg=self.bg,padx=16,pady=12);top.pack(fill='x')
        self.label(top,'Lecteur :',11).pack(side='left')
        self.drives=ttk.Combobox(top,textvariable=self.drive,width=14,state='readonly');self.drives.pack(side='left',padx=10)
        self.btn(top,'⟳  Actualiser / Lire le CD',self.refresh).pack(side='left')
        self.btn(top,'🌐  Rechercher les titres',self.search).pack(side='left',padx=12)
        tk.Checkbutton(top,text='Recherche automatique',variable=self.autofetch,bg=self.bg,fg=self.fg,selectcolor=self.panel,activebackground=self.bg,activeforeground=self.fg).pack(side='left')
        main=tk.Frame(self.root,bg=self.bg,padx=16);main.pack(fill='both',expand=True)
        left=tk.Frame(main,bg=self.bg);left.pack(side='left',fill='both',expand=True,padx=(0,10))
        right=tk.Frame(main,bg=self.bg,width=355);right.pack(side='right',fill='y');right.pack_propagate(False)
        info=self.panel_box(left,'♫  Informations de l’album');info.pack(fill='x',pady=(0,12))
        for i,(txt,var) in enumerate([('Artiste',self.artist),('Album',self.album),('Année',self.year),('Genre',self.genre)]):
            line=tk.Frame(info,bg=self.panel);line.pack(fill='x',pady=3)
            self.label(line,txt+' :',10).pack(side='left');self.entry(line,var).pack(side='right',fill='x',expand=True,padx=(12,0))
        listing=self.panel_box(left,'🎵  Pistes — double-cliquez sur un titre pour le modifier');listing.pack(fill='both',expand=True)
        headers=tk.Frame(listing,bg='#20365a');headers.pack(fill='x')
        for text,width in [('✓',4),('N°',5),('Titre',38),('Durée',8)]:
            self.label(headers,text,10,'#a9c5f4',True).pack(side='left',padx=4)
        wrap=tk.Frame(listing,bg=self.panel);wrap.pack(fill='both',expand=True)
        self.canvas=tk.Canvas(wrap,bg=self.panel,highlightthickness=0);bar=ttk.Scrollbar(wrap,orient='vertical',command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=bar.set);bar.pack(side='right',fill='y');self.canvas.pack(side='left',fill='both',expand=True)
        self.trackframe=tk.Frame(self.canvas,bg=self.panel);self.canvas.create_window((0,0),window=self.trackframe,anchor='nw')
        self.trackframe.bind('<Configure>',lambda e:self.canvas.configure(scrollregion=self.canvas.bbox('all')))
        actions=tk.Frame(left,bg=self.bg);actions.pack(fill='x',pady=10)
        self.btn(actions,'Tout sélectionner',lambda:self.select_all(True)).pack(side='left')
        self.btn(actions,'Tout désélectionner',lambda:self.select_all(False)).pack(side='left',padx=8)
        fmt=self.panel_box(right,'🎚  Format de sortie');fmt.pack(fill='x',pady=(0,12))
        for name,var in [('WAV',self.want_wav),('FLAC',self.want_flac),('MP3',self.want_mp3)]:
            tk.Checkbutton(fmt,text=name+(' — sans perte' if name in ('WAV','FLAC') else ' — compressé'),variable=var,bg=self.panel,fg=self.fg,selectcolor='#293e65',activebackground=self.panel,activeforeground=self.fg).pack(anchor='w')
        self.label(fmt,'Débit MP3 (kb/s) :',10).pack(anchor='w',pady=(9,3))
        ttk.Combobox(fmt,textvariable=self.bitrate,values=['128','192','256','320'],state='readonly',width=12).pack(anchor='w')
        dest=self.panel_box(right,'📁  Destination');dest.pack(fill='x',pady=(0,12))
        self.entry(dest,self.folder,29).pack(fill='x',pady=5)
        self.btn(dest,'Parcourir…',self.browse).pack(anchor='e')
        self.label(dest,'Classement : Artiste / Album (année) / Format / 01 - Titre',9,'#9fc0eb').pack(anchor='w',pady=6)
        opts=self.panel_box(right,'⚙  Options');opts.pack(fill='x')
        self.label(opts,'• Tags MP3 et FLAC : artiste, album, piste, année, genre',10).pack(anchor='w',pady=4)
        self.label(opts,'• Les titres restent modifiables avant extraction',10).pack(anchor='w',pady=4)
        self.label(opts,'• Lecture numérique du CD audio',10).pack(anchor='w',pady=4)
        soundbox=self.panel_box(right,'🔔  Notifications sonores');soundbox.pack(fill='x',pady=(12,0))
        for title,var,kind in [('Fin d’extraction',self.sound_success,'success'),('Erreur',self.sound_error,'error'),('CD détecté',self.sound_disc,'disc')]:
            line=tk.Frame(soundbox,bg=self.panel);line.pack(fill='x',pady=2)
            tk.Checkbutton(line,text=title,variable=var,bg=self.panel,fg=self.fg,selectcolor='#293e65',activebackground=self.panel,activeforeground=self.fg).pack(side='left')
            self.btn(line,'▶',lambda k=kind:self.play_sound(k)).pack(side='right')
        self.btn(right,'💿  EXTRAIRE LES PISTES',self.extract,'#8a35d5').pack(fill='x',pady=16,ipady=10)
        foot=tk.Frame(self.root,bg=self.bg,padx=16,pady=12);foot.pack(fill='x')
        self.progress=ttk.Progressbar(foot,maximum=100);self.progress.pack(fill='x',pady=4)
        self.label(foot,'Statut :',10,self.cyan).pack(side='left')
        self.label(foot,'',10).destroy()
        tk.Label(foot,textvariable=self.status,bg=self.bg,fg=self.fg,font=('Segoe UI',10)).pack(side='left',padx=8)
    def play_sound(self,kind):
        names={'success':'01_succes_p_etincelant.wav','error':'04_erreur.wav','disc':'05_cd_detecte.wav'}
        base=Path(getattr(sys,'_MEIPASS',Path(__file__).parent))
        path=base/'sounds'/names[kind]
        if path.is_file():
            try: winsound.PlaySound(str(path),winsound.SND_FILENAME|winsound.SND_ASYNC|winsound.SND_NODEFAULT)
            except RuntimeError: pass
    def browse(self):
        d=filedialog.askdirectory(initialdir=self.folder.get());
        if d:self.folder.set(d)
    def select_all(self,val):
        for check,title,dur in self.entries:check.set(val)
    def refresh(self):
        ds=drive_letters();self.drives['values']=ds
        if not ds:self.status.set('Aucun lecteur CD/DVD détecté.');return
        if self.drive.get() not in ds:self.drive.set(ds[0])
        self.run_thread(self.load)
    def load(self):
        cd=None
        try:
            cd=CD(self.drive.get()); tracks=cd.toc
            if any(t['control']&4 for t in tracks): raise ValueError('Ce disque contient une piste de données ; extraction audio uniquement.')
            self.root.after(0,lambda:self.show_tracks(tracks))
            if self.autofetch.get():self.root.after(400,self.search)
        except Exception as e:self.set_status('Lecture impossible : '+str(e))
        finally:
            if cd:cd.close()
    def show_tracks(self,tracks):
        self.tracks=tracks;self.entries=[]
        for widget in self.trackframe.winfo_children():widget.destroy()
        for i,t in enumerate(tracks):
            row=tk.Frame(self.trackframe,bg='#142944' if i%2==0 else self.panel);row.pack(fill='x',pady=1)
            check=tk.BooleanVar(value=True);tk.Checkbutton(row,variable=check,bg=row.cget('bg'),selectcolor='#5a2e8e',activebackground=row.cget('bg')).pack(side='left',padx=8)
            self.label(row,f'{t["num"]:02}',10).pack(side='left',padx=8)
            title=tk.StringVar(value=f'Piste {t["num"]:02}');self.entry(row,title,37).pack(side='left',fill='x',expand=True,padx=8,pady=4)
            seconds=max(0,(t['end']-t['lba'])//75)
            self.label(row,f'{seconds//60:02}:{seconds%60:02}',10).pack(side='right',padx=8)
            self.entries.append((check,title,seconds))
        self.status.set(f'{len(tracks)} pistes détectées. Vous pouvez modifier les titres.')
        if self.sound_disc.get():self.play_sound('disc')
    def set_status(self,s):self.root.after(0,lambda:self.status.set(s))
    def run_thread(self,fn):threading.Thread(target=fn,daemon=True).start()
    def search(self):
        if not self.tracks:return
        self.set_status('Recherche des informations sur MusicBrainz…')
        self.run_thread(self.do_search)
    def do_search(self):
        try:
            artist,album,year,names=lookup(self.tracks)
            def update():
                self.artist.set(artist);self.album.set(album);self.year.set(year)
                for i,name in enumerate(names[:len(self.entries)]):self.entries[i][1].set(name)
                self.status.set('Informations de l’album récupérées. Vérifiez les titres avant extraction.')
            self.root.after(0,update)
        except Exception as e:self.set_status('Recherche : '+str(e)+' Vous pouvez saisir les titres manuellement.')
    def extract(self):
        if self.busy:return
        selected=[(self.tracks[i],entry[1].get(),entry[2]) for i,entry in enumerate(self.entries) if entry[0].get()]
        if not selected:messagebox.showwarning(APP,'Sélectionnez au moins une piste.');return
        formats=tuple(f for f,enabled in [('WAV',self.want_wav.get()),('FLAC',self.want_flac.get()),('MP3',self.want_mp3.get())] if enabled)
        if not formats:
            messagebox.showwarning(APP,'Sélectionnez au moins un format.');return
        if any(fmt in formats for fmt in ('MP3','FLAC')) and not ffmpeg_path():
            messagebox.showerror(APP,'ffmpeg.exe est absent. Placez-le à côté de Ripster pour permettre l’encodage MP3/FLAC.');return
        config=(self.drive.get(),formats,self.bitrate.get(),self.folder.get(),self.artist.get(),self.album.get(),self.year.get(),self.genre.get())
        self.busy=True;self.run_thread(lambda:self.do_extract(selected,config))
    def do_extract(self,selected,config):
        drive,formats,bitrate,base,artist,album,year,genre=config
        dest=Path(base)/clean(artist or 'Artiste inconnu')/clean((album or 'Album inconnu')+(f' ({year})' if year else ''))
        folders={fmt:dest/('WAV' if fmt=='WAV' else 'FLAC' if fmt=='FLAC' else f'MP3 {bitrate} kbps') for fmt in formats}
        cd=None
        try:
            # Check every target before starting: never silently overwrite files.
            for t,title,_ in selected:
                name=f'{t["num"]:02} - {clean(title)}'
                for fmt,folder in folders.items():
                    out=folder/(name+'.'+fmt.lower())
                    if out.exists():raise FileExistsError(f'Le fichier existe déjà : {out}. Aucun écrasement automatique.')
            for folder in folders.values():folder.mkdir(parents=True,exist_ok=True)
            cd=CD(drive)
            total=sum(t['end']-t['lba'] for t,_,_ in selected);completed=0
            for t,title,_ in selected:
                name=f'{t["num"]:02} - {clean(title)}'
                # Read the CD once per track. WAV serves as both an output and
                # the intermediate for MP3 and FLAC, avoiding extra CD reads.
                wavpath=(folders['WAV']/(name+'.wav')) if 'WAV' in formats else (dest/(name+'.ripster.tmp.wav'))
                created_wav=False
                try:
                    with wave.open(str(wavpath),'wb') as w:
                        w.setnchannels(2);w.setsampwidth(2);w.setframerate(44100)
                        for lba in range(t['lba'],t['end'],16):
                            n=min(16,t['end']-lba)
                            w.writeframesraw(cd.read_sectors(lba,n))
                            completed+=n
                            pct=int(100*completed/max(1,total))
                            self.root.after(0,lambda p=pct:self.progress.configure(value=p))
                            self.set_status(f'Lecture du CD : {title} — {pct} %')
                    created_wav=True
                    if 'FLAC' in formats:
                        out=folders['FLAC']/(name+'.flac')
                        self.set_status(f'Encodage FLAC : {title}')
                        cmd=[ffmpeg_path(),'-nostdin','-hide_banner','-loglevel','error','-n','-i',str(wavpath),'-codec:a','flac','-compression_level','8','-metadata','title='+title,'-metadata','artist='+artist,'-metadata','album='+album,'-metadata','track='+str(t['num']),'-metadata','date='+year,'-metadata','genre='+genre,str(out)]
                        p=subprocess.run(cmd,creationflags=0x08000000,capture_output=True,text=True)
                        if p.returncode:raise RuntimeError('Encodage FLAC : '+p.stderr[-700:])
                    if 'MP3' in formats:
                        out=folders['MP3']/(name+'.mp3')
                        self.set_status(f'Encodage MP3 : {title}')
                        cmd=[ffmpeg_path(),'-nostdin','-hide_banner','-loglevel','error','-n','-i',str(wavpath),'-codec:a','libmp3lame','-b:a',bitrate+'k','-metadata','title='+title,'-metadata','artist='+artist,'-metadata','album='+album,'-metadata','track='+str(t['num']),'-metadata','date='+year,'-metadata','genre='+genre,str(out)]
                        p=subprocess.run(cmd,creationflags=0x08000000,capture_output=True,text=True)
                        if p.returncode:raise RuntimeError('Encodage MP3 : '+p.stderr[-700:])
                finally:
                    if 'WAV' not in formats and wavpath.exists():wavpath.unlink()
            self.set_status('Terminé ! Fichiers enregistrés dans '+str(dest))
            if self.sound_success.get():self.play_sound('success')
            self.root.after(0,lambda:messagebox.showinfo(APP,'Extraction terminée !\n'+str(dest)))
        except Exception as e:
            self.set_status('Erreur : '+str(e))
            if self.sound_error.get():self.play_sound('error')
            self.root.after(0,lambda msg=str(e):messagebox.showerror(APP,msg))
        finally:
            if cd:cd.close()
            self.busy=False

if __name__=='__main__':
    if os.name!='nt':raise SystemExit('Ripster fonctionne sous Windows uniquement.')
    root=tk.Tk();App(root);root.mainloop()
