#!/usr/bin/python
#
# fexit - a F*EX client for Windows (and UNIX)
#
# Ulli Horlacher <framstag@rus.uni-stuttgart.de>
#
# Perl Artistic Licence

from __future__ import print_function
from zipfile import ZipFile,ZIP_DEFLATED
from inspect import currentframe
from base64 import b64encode,b64decode
from getopt import getopt,GetoptError
from time import time,strftime,localtime,sleep
from glob import glob
from os import environ,getenv,system,path,walk,access,stat,lstat
from os import mkdir,makedirs,chdir,listdir,getcwd,remove,rename
import os
import re
import sys
import shlex
import socket
import signal
import random
import string
import tarfile
import platform
import traceback
import subprocess

try:
  import msvcrt
  import win32clipboard
  try:    import _winreg as winreg
  except: import winreg
except ImportError:
  import tty
  import fcntl
  import select
  import termios

version = 0

usage = '''
upload usage: fexit [-c "comment"] [-a container] file(s) recipient[,...]
example: fexit flupp.avi framstag@rus.uni-stuttgart.de
example: fexit -c "lab research" -a data *.png x1@flupp.org,x2@flupp.org

download usage: fexit FEX-download-URL
example: fexit http://fex.rus.uni-stuttgart.de/fop/jHn34yp7/flupp.avi

help: fexit -H
'''

more_usage = '''
additional options:
  -v                               # HTTP verbose output
  -u fexserver/user@domain:auth-ID # use this server & user
  -o                               # overwrite file
  -d                               # delete file
  -x [files]                       # F*EX clipboard read/write
  -s [files]                       # SEX read/write yourself
  -m kBs                           # max kBs throuput
  -k days                          # keep file days on server
  -T up-MBs[:down-MBs] [server]    # test internet speed
  -X "parameter"                   # additional URI parameter
  -X?                              # show recipients parameter
  
special recipients:
  .                # yourself, without notification email
  [any character]  # saved address
'''

#or save them in versioned archives on the fexserver.
doc = '''
With fexit you can send files or directories of any size to any email address.

To use a proxy set the environment variable HTTP_PROXY.
At any prompt you can enter [?] for specific help or [Ctrl]+[C] to go back.
When you run fexit via command console (cmd) you can specify options and
arguments. See "fexit -h" for usage help.
You can also drag and drop files to the fexit icon on your desktop.
See http://fex.rus.uni-stuttgart.de/ for more information about F*EX.
'''

python2 = sys.version_info[0] == 2
python3 = sys.version_info[0] == 3

if python2: import urllib2 as urllib
if python3: import urllib.request as urllib

macos   = platform.system() == 'Darwin'
windoof = platform.system() == 'Windows'
linux   = platform.system() == 'Linux'

GUI = windoof or getenv('DISPLAY') and environ['TERM'] != 'screen'
if GUI:
  try:
    global Tk,askopenfilename,askdirectory
    if python2:
      from Tkinter import Tk
      from tkFileDialog import askopenfilename,askdirectory
    if python3:
      from tkinter import Tk
      from tkinter.filedialog import askopenfilename,askdirectory
  except:
    GUI = False

kB = 2**10
kB4 = 4*kB
kB64 = 64*kB
MB = 2**20
GB = 2**30

def main():
  global _ 	# default string
  global opts	# CLI options dictionary
  global args   # CLI arguments
  global prg
  global version,usage,doc,more_usage
  global HOME
  global fexhome,tmpdir,idf,addressesf,editor,useragent
  global userurl,fexurl,server,port,user,aid
  global skey,gkey
  global sock,timeout
  global verbose,overwrite,delete,maxtp,keep
  global archive,ddir,fddir
  global proxy,proxy_prefix
  global features
  global arecipient
  global sss

  version = version or mtime(sys.argv[0],'%Y%m%d')

  verbose = delete = overwrite = maxtp = keep = 0
  arecipient = qrecipient = ''
  archive = ddir = ''
  skey = gkey = ''
  userurl = fexurl = server = user = aid = ''
  features = ''
  sss = 0
  opts = []
  timeout = 60
  port = 80

  if windoof:
    prg = sys.argv[0]
    if prg.find('fexit_new.exe') >= 0:
      sleep(1)
      fexit = subst('fexit_new.exe','fexit.exe',prg)
      if path.exists(fexit): 
        remove(fexit)
      if path.exists(fexit):
        try: syscall('del',fexit)
        except: pass
      sleep(1)
      rename(prg,fexit)
      os.execl(fexit,fexit)
    HOME = environ['USERPROFILE']
    if 'FEXHOME' in environ: fexhome = environ['FEXHOME']
    else:                    fexhome = HOME+'\\fex'
    if 'FEXTMP' in environ: tmpdir = environ['FEXTMP']
    elif 'TEMP' in environ: tmpdir = environ['TEMP']+'\\fex'
    elif 'TMP'  in environ: tmpdir = environ['TMP']+'\\fex'
    else:                   tmpdir = fexhome+'\\tmp'
    idf = fexhome+'\\id'
    addressesf = fexhome+'\\addresses'
    pv = platform.version()
    ddir = HOME+'\\Downloads\\fex'
    fddir = fexhome+'\\Downloads'
  else:
    import readline
    readline.parse_and_bind("tab: complete")
    readline.set_completer_delims(
      "".join(c for c in readline.get_completer_delims() if c != "/"))
    prg = path.basename(sys.argv[0])
    HOME = environ['HOME']
    try:    fexhome = environ['FEXHOME']
    except: fexhome = HOME+'/.fex'
    try:    tmpdir = environ['FEXTMP']
    except: tmpdir = fexhome+'/tmp'
    idf = fexhome+'/id'
    addressesf = fexhome+'/addresses'
    if macos:
      pv = shcmd("sw_vers -productVersion 2>/dev/null")
    else:
      pv = shcmd("lsb_release -d 2>/dev/null")
      if len(pv) > 3:
        pv = subst(r"Description:\s+",'',pv)
      else:
        pv = platform.version()
        pv = subst(r" [A-Z]+ [A-Z][a-z][a-z] [A-Z][a-z][a-z] \d.*",'',pv)
        pv = subst(r"#\d+-",'',pv)
    ddir = ''

  useragent = "fexit-%s on %s %s %s" % \
              (version,platform.system(),platform.release(),pv)

  doc = strip(doc)

  if path.exists(idf): 
    doc += "\nYour login data (user, server, auth-ID) is stored in\n" + idf

  tmkdir(fexhome)
  tmkdir(tmpdir)
  if ddir: tmkdir(ddir)

  get_opt_arg("hHvodxsMAu:U:C:c:m:k:X:a:T:")
  comment = opts.get('C') or opts.get('c') or ''
  if 'd' in opts: delete = comment = 'DELETE'
  if 'o' in opts: overwrite = opts['o']
  if 'v' in opts: verbose = opts['v']
  if 'a' in opts: archive = opts['a']
  if 'u' in opts: fexurl = opts['u']
  try:    maxtp = int(opts['m'])
  except: maxtp = 0
  try:    keep = int(opts['k'])
  except: keep = 0

  get_proxy()
  get_ID()

  if 'H' in opts:
    usage = subst('\nhelp:.*\n',more_usage,usage)
    printf("\n%s\n%s",doc,usage)
    return 0

  if 'T' in opts:
    usage = "usage: fexit -T MB_up[:MB_down] [fexserver]"
    if _m(r'^(\d+)$',opts['T']):
      up = down = int(_1)
    elif _m(r'^(\d+):(\d+)$',opts['T']):
      up = int(_1)
      down = int(_2)
    else:
      die(usage)

    if args:
      return nettest(args[0],up,down)
    else:
      return nettest('fex.belwue.de',up,down)

#  if user and 'A' in opts:
#    ddir = '.'
#    manage_archives()
#    print()
#    return(0)
    
  if user and 'x' in opts:
    if args:
      return xx_send(args)
    else:
      return xx_get('.')

  if user and 's' in opts:
    if args:
      return sex_send(args)
    else:
      return sex_get('.')

  if not args:
    if windoof:
      fexit = sys.argv[0]
      sendto = HOME+r'\AppData\Roaming\Microsoft\Windows\SendTo\fexit.exe'
      if (fexit.find('fexit.exe') >= 0
          and fexit != sendto and not path.exists(sendto)):
        cmd = ['copy',fexit,sendto]
        cmd = ['mklink','/H',sendto,fexit]
        try: syscall(cmd)
        except: pass
      desktop = HOME + '\\Desktop'
      if fexit.find(desktop) == 0 and getenv('PATH').find(desktop) < 0:
        set_path(desktop)
    menu()
    os._exit(0)

  if len(args) == 1:
    arg = args[0]
    if match('^http.*/fop/',arg):
      if delete:
        status = fexdel(arg)
      else:
        try:
          status = fexget(arg)
        except KeyboardInterrupt:
          eprintf("\n*interrupted*\n")
          status = 99
      if type(status) is not int: status = 0
      if status is None: status = 9
      return status

  if len(args) > 1 and args[-1] == '.':
    arecipient = recipient = '.'
    args = args[:-1]
#  elif len(args) > 1 and (args[-1] == '_' or args[-1] == 'A'):
#    arecipient = recipient = '_'
#    args = args[:-1]
  elif len(args) > 1 and args[-1] == 'X':
    arecipient = recipient = '.'
    archive = 'STDFEX.tgz'
    args = args[:-1]
  else:
    recipient = ''

  if len(args) > 1 and not recipient and not path.exists(args[-1]):
    arecipient = recipient = args[-1]
    args = args[:-1]
    read_addresses()
    if recipient in address: recipient = address[recipient]

  #files = [subst(r'([/\\])+$','',file) for file in args]
  files = []
  for file in args:
    if not path.exists(file):
      die('"%s" does not exist' % file)
    if not (path.isfile(file) or path.isdir(file)):
      die('"%s" is not a file or directory' % file)
    if not access(file,os.R_OK):
      die('"%s" is not readable' % file)
    nrf = not_readable(file)
    if len(nrf):
      warn('files not readable:')
      for file in nrf: eprintf('%s\n',file)
      wexit(1)
    if match('-',file_id(file)):
      die('some files are not readable')
    files.append(file)
    print("           \r")
    print('\n"%s"' % file)
    print(mtime(file))
    print(kMG(file_size([file])))

  if recipient == '':
    qrecipient = recipient = ask_recipient()
    if recipient is None or recipient == '': wexit(0)
    if recipient == 'fex clipboard':
      archive = 'STDFEX.tgz'
      recipient = '.'
    if recipient != '.' and not comment:
      if recipient == 'fex archive': recipient = '_'
      comment = inputline("Comment: ")
      if comment is None: wexit(0)

  # extra URI parameter in comment?
  comment = XUP(comment)

  print()

  if match('^https?://',recipient): get_sgkey(recipient)
  if not (gkey or skey or aid or 'u' in opts): set_ID()

  try:
    status = sendfile_retry(files,recipient,comment)
  except KeyboardInterrupt:
    eprintf("\n*interrupted*\n")
    status = 99
  print()
  if archive: save_remove(archive)
  if qrecipient and status == 200: remember_recipient(recipient)
  if status is None: status = 9
  if status == 0:    status = 1
  if status == 200:  status = 0
  return status


def menu():
  help = ''
  mopts = not user

  while True:
    cls()
    printf("\n%s\n%s\n\n",useragent,'-' * len(useragent))
    if user:
      print("User: %s" % user)
      print("Server: %s" % fexurl)
    if proxy:
      print("Proxy: %s" % proxy)
    if help:
      print()
      print(help)
      print("\nEnter [m] for more options.\n")
      help = ''
      k = prompt_key('Press [ENTER] to continue')
      if k == 'm': mopts = k
      continue
    print()
    print("key  action")
    print("[s]  send a file or directory (upload)")
    print("[g]  get a file (download)")
    if user:
#     print("[a]  manage archives")
      print("[x]  extract fex clipboard")
      print("[e]  edit address list")
      print("[l]  login with webbrowser")
    if mopts:
      print("[C]  change login data (user, server, auth-ID)")
      print("[T]  test internet speed")
    print("[u]  update fexit")
    print("[?]  help")
    print("[q]  quit")
    print()
    k = prompt_key("Select action key: [ ]\b\b")
    # print("[%s]" % k)

    if k == '\r' or k == '\n': continue

    if k == 'm':
      print(k)
      mopts = k
      continue

    if k == 's':
      print(k)
      ask_file()
      continue

    if k == 'g':
      print(k)
      # https://stackoverflow.com/questions/101128/how-do-i-read-text-from-the-windows-clipboard-from-python
      try: durl = despace(inputline("\nF*EX download URL: "))
      except: continue
      if durl:
        if ddir:
          try:
            chdir(ddir)
          except (IOError,OSError) as e:
            warn('cannot chdir "%s" - %s' % (ddir,e.strerror))
            continue
        try:
          status = fexget(durl)
          if windoof:
            if type(status) is not int: subprocess.call(['explorer',ddir])
        except KeyboardInterrupt:
          eprintf("\n*interrupted*\n")
          sleep(1)
        inputline('\nPress [ENTER] to continue')
      continue

#    if k == 'a':
#      print(k)
#      manage_archives()
#      continue

    if k == 'x':
      print(k)
      if not aid: get_ID()
      xx_get()
      inputline('Press [ENTER] to continue')
      continue

    if k == 'u':
      print(k)
      update()
      continue

    if k == 'e':
      print(k)
      edit_addresses()
      continue

    if k == 'l':
      print(k)
      if GUI:
        if windoof:
          syscall('start','',userurl)
        else:
          system('xdg-open %s || firefox %s' % (userurl,userurl))
      else:
        print("function not available - no GUI")
      sleep(3)
      continue

    if k == 'C':
      print(k)
      set_ID()
      get_ID()
      inputline('\nPress [ENTER] to continue')
      continue

    if k == 'T':
      # nettest
      print(k)
      cls()
      # tfs = server or 'fex.belwue.de'
      tfs = 'fex.belwue.de'
      print("Test internet speed with %s\n" % tfs)
      if port: tfs += ':80'
      up = inputline("MBs to send: ")
      if up is None: continue
      if _m(r'(\d+)',up): up = int(_1)
      else: up = 0
      down = inputline("MBs to receive: ")
      if down is None: continue
      if _m(r'(\d+)',down): down = int(_1)
      else: down = 0
      if up+down:
        print()
        syscall(sys.argv[0],'-T',"%d:%d" % (up,down))
        # get_ID()
        inputline('\nPress [ENTER] to continue')
      continue

    if k == 'h' or k == '?':
      print(k)
      help = doc
      continue

    if k in list('q\003\004'):
      print('q')
      print("\nSee you next time! :-)\n")
      sleep(1)
      os._exit(0)
      wexit(0)

    # https://docs.python.org/2/library/winsound.html
    print('\007unknown key]')
    sleep(1)


def get_ID():
  global fexurl,user,aid

  if 'u' in opts:
    fexurl = opts['u']
  else:
    FEXID = getenv('FEXXX') or getenv('FEXID')
    if FEXID:
      try:
        if match(r'^\S+$',FEXID): FEXID = b64decode(b64fix(FEXID))
        fexurl,user,aid = FEXID.split()
      except:
        die('illegal $FEXID format')
    else:
      try:
        idfo = open(idf,'r')
        fexurl = despace(getline(idfo))
        user   = despace(getline(idfo))
        aid    = despace(getline(idfo))
        if verbose: print("reading ID data from "+idf)
        while getline(idfo) is not None:
          if _ == '[xx]':
            fexurl = despace(getline(idfo))
            user   = despace(getline(idfo))
            aid    = despace(getline(idfo))
            break
        idfo.close()
      except:
        pass

  if fexurl:
    parse_url(fexurl)
    #check_7z()


def set_ID():
  global fexurl,user,aid

  print()
  print("You have to enter your F*EX authorization data "
        "(server, user, auth-ID)")
  print()
  print("Terminate each input line with [ENTER]")
  print('You can always enter [?] for help.')

  while True:
    user = aid = ''
    print()
    fexurl = inputline("F*EX server URL: ")
    if fexurl is None: return
    fexurl = despace(fexurl)
    if fexurl == '?':
      print("Enter the address of your F*EX server where you are registered.")
      print("You may also copy&paste your personal F*EX login URL.")
      continue
    if not match(r"\w",fexurl): continue
    parse_url(fexurl)
    http_connect(server,port)
    if not sock: continue
    reply,header,body = http_request(
      "GET %s/logo.jpg HTTP/1.0" % proxy_prefix,
      server,port,
    )
    if not reply or not match('^HTTP.* 200',reply):
      warn('no F*EX server at %s:%d' % (server,port))
      continue
    if not body or len(body) < 9999:
      eprintf('Bad response from %s:%d' % (server,port))
      continue

    logo = path.join(tmpdir,'fex.jpg')
    try:
      logoo = open(logo,'wb')
      logoo.write(body)
      logoo.close()
      if verbose: printf("%s written\n",logo)
    except (IOError,OSError) as e:
      die('cannot write "%s" - %s' % (logo,e.strerror))

    if not aid:
      while not user:
        user = inputline("Your account on %s: " % server)
        if user is None: return
        user = despace(user)
        if user == '?':
          print("Enter your email address.")
          user = ''
      while not aid:
        aid = inputline("Your auth-ID: ")
        if aid is None: return
        aid = despace(aid)
        if aid == '?':
          printf("Enter your auth-ID for %s on %s.",user,fexurl)
          print('If you do not know your auth-ID, then see "user config" at')
          print(fexurl)
          aid = ''

    try:
      idfo = open(idf,'w')
      print("%s:%d" % (server,port),file=idfo)
      print(user,file=idfo)
      print(aid,file=idfo)
      idfo.close()
      if verbose: printf("%s written\n",idf)
    except (IOError,OSError) as e:
      die('cannot write "%s" - %s' % (idf,e.strerror))

    get_ID()

    print("\nSending test file...\n")
    status = sendfile_retry([logo],user,comment='fexit test!')
    if status == 200: return
    die("failed with status=%d" % status)


def remember_recipient(recipient):
  global _
  global address

  recipient = recipient.lower()
  read_addresses()

  if (not recipient in address.values() 
      and recipient != user and recipient != '.' and recipient != '_'):
    while True:
      k = prompt_key("Assign %s to [ ]\b\b" % recipient)
      if k == '?':
        print(k)
        print()
        print("fexit can remember email addresses of your recipients.")
        print("Each address can be assigned to a key and saved.")
        print("You can now enter any key or press [ENTER] for no key.")
        print()
        continue
      if k == 'X':
        print(k)
        printf("\n[X] is reserved for the fex clipboard. ")
        print("You cannot assign an address to it.\n")
        continue
      if k == 'A':
        print(k)
        printf("\n[A] is reserved for the fex archive. ")
        print("You cannot assign an address to it.\n")
        continue
      if k == '.': continue
      if k > ' ':
        print(k)
        address[k] = recipient
      else:
        print()
      break

  if recipient != user and recipient != '.' and recipient != '_':
    address[' '] = recipient
  save_addresses()


def read_addresses():
  global address

  address = {}

  try:
    afo = open(addressesf,'r')
    while getline(afo) != None:
      if _m(r'^(.) (.+)'): address[_1] = _2
    afo.close()
  except:
    pass

  if '.' in address: del address['.']
  if 'X' in address: del address['X']
  if 'A' in address: del address['A']
  if user: address['m'] = user


def edit_addresses():
  global _
  global address

  read_addresses()
  address['m'] = user

  while True:
    cls()
    print("fexit can remember email addresses of your recipients.")
    print("Each address can be assigned to a key.")
    print("You can now enter a new key to assign a recipient email address or")
    print("enter an existing key to reassign a recipient email address.")
    print()
    akeys = 0
    for (k,a) in sorted(address.items()):
      if not k in list(' ._-mXA'): 
        if not akeys:
          akeys = 1
          print("key  address")
        printf("[%s]  %s\n",k,a)
    print()
    print("[any key]    assign address")
    if akeys:
      print("[SPACE]      delete address")
      print("[m]          move address")
    print("[BACKSPACE]  back to main menu without saving")
    print("[ENTER]      save address list and back to main menu")
    print()
    sleep(1)
    while True:
      k = prompt_key("Key: [ ]\b\b")
      if k in list('\b\177\003\004'): return
      if k == '\n' or k == '\r':
        print()
        save_addresses()
        return
      if k < ' ': continue
      if k == ' ':
        k = prompt_key("Delete key: [ ]\b\b")
        if k == '\003' or k == '\004': return
        if k <= ' ' or k in list('.?\177'): break
        print(k)
        if not k in address:
          print("There is no address for this key")
          sleep(2)
          break
        del address[k]
        break
      if k == 'm':
        k = prompt_key("Move key: [ ]\b\b")
        if k == '\003' or k == '\004': return
        if k <= ' ' or k in list('.?\177'): break
        print(k)
        if not k in address or k == 'm':
          print("There is no address for this key")
          sleep(2)
          break
        n = prompt_key("Move %s to key: [ ]\b\b" % address[k])
        if n == '\003' or n == '\004': return
        if n == k: break
        if n < ' ' or n in list('.?\177'): break
        if n == 'm':
          print(n)
          printf("\n%s is your user email address at\n%s\n",user,fexurl)
          print("It is hardwired to [m], you cannot change it.\n")
          inputline('Press [ENTER] to continue')
          break
        if n == 'X':
          print(n)
          printf("\n[X] is reserved for the fex clipboard. ")
          print("You cannot assign an address to it.\n")
          inputline('Press [ENTER] to continue')
          break
        print(n)
        address[n] = address[k]
        del address[k]
        break
      if k in list('._-XA'):
        print(k)
        print("[%s] is a reserved key. You cannot assign it.\n" % k)
        sleep(2)
        break
      print(k)
      recipient = inputline("Recipient(s): ")
      if recipient is None: break
      recipient = subst('[ ,;]+',',',recipient)
      if recipient == '' and k in address: del address[k]
      if match(r'\w',recipient): address[k] = recipient
      break


def save_addresses():
  try:
    afo = open(addressesf,'w')
    for (k,a) in sorted(address.items()):
      if not k in list('mx'): print("%s %s" % (k,a),file=afo)
    afo.close()
  except (IOError,OSError) as e:
    die('cannot write "%s" - %s' % (addressesf,e.strerror))


def parse_url(url):
  global server,port,proxy,proxy_prefix,user,aid,fexurl,userurl

  url = despace(url)
  port = 80
  proxy = proxy_prefix = ''
  user = user
  aid = aid
  fexurl = fexurl
  userurl = userurl
  
  if _m(r"!(([\w.-]+):(\d+))$",url):
    proxy = _1
    server = _2
    port = int(_3)
    proxy_prefix = subst("!.*",'',url)

    if port == 443 and not match("https://|:443",proxy_prefix):
      die("error in %s: " % idf +
          "fexserver and proxy must both use port 443 for https")

    if _m(r"/(.+@.+):(.+)$",proxy_prefix):
      user = _1
      aid = _2
      proxy_prefix = subst('/.*','',proxy_prefix)

    if _m(r"/fup/(\w+)$",proxy_prefix):
      up = b64decode(b64fix(_1))
      if _m(r"(from|user)=(.+)&id=(.+)",up):
        user = _2
        aid = _3

    userurl = proxy_prefix+'/fup/'+b64e('from=%s&id=%s' % (user,aid))

  else:
    if _m(r"/(.+@.+):(.+)$",url):
      user = _1
      aid = _2
      url = subst('/.*','',url)

    if _m(r"/fup/(\w+)$",url):
      up = b64decode(b64fix(_1))
      if _m(r"(from|user)=(.+)&id=(.+)",up):
        user = _2
        aid = _3

    if match('https://',url): port = 443
    server = subst('https?://','',url)
    if _m(r'(.+):(\d+)',server):
      server = _1
      port = int(_2)
    server = subst('/.*','',server)

    if port == 443:
      fexurl = 'https://'+server
    elif port == 80:
      fexurl = 'http://'+server
    else:
      fexurl = 'http://%s:%d' % (server,port)

    userurl = fexurl+'/fup/'+b64e('from=%s&id=%s' % (user,aid))

  return server,port,proxy,proxy_prefix,user,aid,fexurl,userurl

def http_connect(server,port):
  global sock
  global proxy_prefix

  sock = None
  proxy_prefix = ''

  if not server: die("internal error in http_connect() - no server")
  if not port:   die("internal error in http_connect() - no port")
  
  if proxy:
    if _m(r"([\w.-]+):(\d+)",proxy):
      ps = _1
      pp = int(_2)
      if port == 443 and pp != 443:
        warnw("fexserver and proxy must both use port 443 for https")
        return
      if verbose: printf("TCPCONNECT to %s:%d\n",ps,pp)
      try:
        sock = socket.create_connection((ps,pp))
      except socket.error as e:
        warnw("cannot connect to %s:%d - %s\n" % (ps,pp,e.strerror))
        return
      if (port == 443):
        http_request("CONNECT %s:%d HTTP/1.1" % (server,port))
      else:
        proxy_prefix = "http://%s:%d" % (server,port)
    else:
      warnw("unknown proxy address format %s" % proxy)
      return
  else:
    if verbose: printf("TCPCONNECT to %s:%d\n",server,port)
    try:
      sock = socket.create_connection((server,port))
    except socket.error as e:
      warnw("cannot connect to %s:%d - %s\n" % (server,port,e.strerror))
      return

  sock.settimeout(timeout)

  if port == 443:
    import ssl
    
    # http://stackoverflow.com/questions/14102416/python-requests-requests-exceptions-sslerror-errno-8-ssl-c504-eof-occurred
    #from functools import wraps
    #def sslwrap(func):
    #  @wraps(func)
    #  def bar(*args,**kw):
    #    kw['ssl_version'] = ssl.PROTOCOL_TLSv1
    #    return func(*args,**kw)
    #  return bar
  
    sock = ssl.wrap_socket(sock)


def http_request(request,server='',port=0,header=None,connection=None):
  cl = -1
  header = header or []
  if server: header.append("Host: %s:%d" % (server,port))
  header.append("User-Agent: "+useragent)
  if connection: header.append(connection)
  header.append('')
  nvt_send(request)
  for line in header:
    nvt_send(line)
  header = []
  reply = nvt_get()
  if reply is None: return reply,[],[]
  while True:
    line = nvt_get()
    if line is None: return reply,header,[]
    if line == '': break
    header.append(line)
    if _m(r"Content-Length:\s+(\d+)",line): cl = int(_1)

  if match('^(GET|POST) /sex',request): return reply,header,[]

  body = []
  if match('^(GET|POST)',request):
    if cl > 0:
      body = receive(cl)
    elif cl == -1:
      while True:
        line = nvt_get(verbose=0)
        if line is None: break
        body.append(line)

  return reply,header,body


def nvt_send(line):
  if verbose: print('-->',line)
  try:
    send(line+"\r\n")
  except socket.error as e:
    die("cannot send to %s:%d - %s" % (server,port,e.strerror))


def nvt_get(verbose=None):
  global _

  if verbose is None: verbose = globals()['verbose']
  line = ''
  _ = None

  while True:
    try:
      c = sock.recv(1)
    except socket.error as e:
      die("cannot read from %s:%d - %s" % (server,port,e.strerror))
    if python3: c = c.decode('iso-8859-1')
    if c == '': break
    line += c
    if c == "\n": break

  if c == '':
    # die("%s:%d has closed the connection" % (server,port))
    if len(line) == 0: return None

  if python3: line = line.encode('iso-8859-1').decode('utf8')
  line = subst("\r?\n",'',line)
  if verbose: print("<--",line)
  _ = line
  return line


def send(s):
  try:
    s = s.encode('utf8')
  except UnicodeDecodeError:
    s = s.decode('iso-8859-1').encode('utf8')
  sock.sendall(s)


def receive(nb):
  bs = kB4
  bb = ''

  while True:
    s = len(bb)
    if s == nb: break
    if s+bs > nb: bs = nb-s
    try:
      b = sock.recv(bs)
    except socket.error as e:
      die("cannot read from %s:%d - %s" % (server,port,e.strerror))
    bb += b

  return(bb)


def md5h(s):
  try:
    s = s.encode('utf8')
  except UnicodeDecodeError:
    s = s.decode('iso-8859-1').encode('utf8')

  if python2:
    import md5
    return md5.new(s).hexdigest()
  if python3:
    import hashlib
    return hashlib.new('md5',s).hexdigest()


def prompt_key(prompt):
  printf('\r                                                    \r')
  printf(prompt)
  clear_keyboard_buffer()
  return get_key()


def clear_keyboard_buffer():
  if windoof:
    while msvcrt.kbhit(): msvcrt.getwch()
  else:
    # https://docs.python.org/2/faq/library.html#how-do-i-get-a-single-keypress-at-a-time
    fd = sys.stdin.fileno()
    fcntl_flags = fcntl.fcntl(fd,fcntl.F_GETFL)
    fcntl.fcntl(fd,fcntl.F_SETFL,fcntl_flags|os.O_NONBLOCK)
    try:
      while sys.stdin.read(1): pass
    except:
      pass
    fcntl.fcntl(fd,fcntl.F_SETFL,fcntl_flags)
    #while len(select.select([fd],[],[],0.0)[0]) > 0: os.read(fd,1)
    #termios.tcflush(sys.stdin,termios.TCIOFLUSH)


# http://stackoverflow.com/questions/510357/python-read-a-single-character-from-the-user
def get_key():
  if windoof:
    k = msvcrt.getch()
  else:
    fd = sys.stdin.fileno()
    tc = termios.tcgetattr(fd)
    try:
      tty.setraw(fd)
      k = sys.stdin.read(1)
    finally:
      termios.tcsetattr(fd,termios.TCSADRAIN,tc)

  if k == '\033':
    clear_keyboard_buffer()
    return get_key()
  else:
    return k


def ask_file(recipient=''):
  global archive

  archive = ''
  files = []
  cls()
  print("\nYou can also drag&drop files to the fexit icon.\n")
  while not recipient:
    recipient = ask_recipient()

    if recipient is None: return
    if recipient == '': continue
    if recipient == '?':
      print()
      print('A recipient is an email address or a '
            'F*EX subuser or groupuser upload URL.')
      print('You can enter also a list of email addresses.')
      print('[Ctrl]+[C] brings you back to the main menu.')
      recipient = ''
      continue
    if match('^https?://',recipient): get_sgkey(recipient)
    if match(r"\w",recipient) or recipient == '.' or recipient == '_': break

  if not (gkey or skey or aid or 'u' in opts): set_ID()

  if GUI:
    while True:
      print()
      if len(files):
        print('[f] select another file')
        print('[d] select another directory')
        # if windoof: print('[&] drag&drop another file or directory')
        print('[l] list selected files')
        print('[ENTER] continue with file processing')
      else:
        print('[f] select a file')
        print('[d] select a directory')
        # if windoof: print('[&] drag&drop a file or directory')
      print()
      k = prompt_key("Select action: [ ]\b\b")
      if k in list('\b\177\003\004'):
        print()
        return
      if k == 'h' or k == '?':
        print(k)
        print('\nYou must select a file or directory.')
        continue
      if k == '\n' or k == '\r':
        print('\n')
        if len(files): break
      if k == 'l':
        print(k)
        for file in files:
          print('\n"%s"' % file)
          print(mtime(file))
          print(kMG(file_size([file])))
      if k == 'f':
        print(k)
        Tk().withdraw()
        file = askopenfilename(title='select a file',initialdir=HOME) or ''
        set_window_focus()
        if file is None or file == '': continue
        print('\nFile selected:\n"%s"' % file)
        if not_readable(file) or match('-',file_id(file)):
          warn('file not readable')
        else:
          printf('%s\n%s\n',mtime(file),kMG(file_size([file])))
          if not file in files: files.append(file)
        print("           \r")
      if k == 'd':
        print(k)
        Tk().withdraw()
        dir = askdirectory(title='select a directory',initialdir=HOME) or ''
        if windoof: dir = subst('/',r'\\',dir)
        set_window_focus()
        if dir is None or dir == '': continue
        print('\nDirectory selected:\n"%s"' % dir)
        if not match('-',file_id(dir)):
          printf('%s\n%s\n',mtime(dir),kMG(file_size([dir])))
          if not dir in files: files.append(dir)
        print("           \r")
      if windoof and k == '&':
        print()
        print("Drag&drop files or directories into this window.")
        print("Only files with ASCII filenames are supported!")
        subprocess.call(['explorer',HOME])
        while True:
          file = get_paste()
          #file = inputline()
          if file is None: return
          if file == '':
            if len(files): break
            else: continue
          if file == '?':
            print("With Windows explorer select a file with the left mouse button.")
            print("Move the mouse into this window while you keep the button pressed.")
            print("Then release the mouse button.")
            print("[Ctrl]+[C] brings you back to the main menu.")
            continue
          print('\n"%s"' % file)
          file = subst(r'[/\\]+$','',file)
          if not(path.exists(file)):
            print('does not exist')
            continue
          if not(path.isfile(file) or path.isdir(file)):
            print('is not a file or directory')
            continue
          if not(access(file,os.R_OK)):
            print('is not readable')
            continue
          if file in files:
            print('is already selected')
            continue
          nrf = not_readable(file)
          if len(nrf):
            if len(nrf) == 1 and nrf[0] == file:
              print('file not readable')
            else:
              print('files not readable:')
              for file in nrf: printf('  %s\n',file)
            continue
          if match('-',file_id(file)):
            print('some files are not readable')
            continue
          print("           \r")
          print(mtime(file))
          print(kMG(file_size([file])))
          if not file in files: files.append(file)
          break
  else:
    while True:
      if recipient == '_' or recipient == 'fex archive':
        file = inputline("File to save: ")
      else: 
        file = inputline("File to send: ")
      if file is None: return
      if files and file == '': break
      if file == '': return
      if file == '?':
        print("Enter your filename (with path) or "
              "press [Ctrl]+[C] to return to main menu.")
        print("Press [ENTER] to continue.")
        continue
      file = subst(r'[/\\]+$','',file)
      if not(path.exists(file)):
        print('              does not exist')
        continue
      if not(path.isfile(file) or path.isdir(file)):
        print('              is not a file or directory')
        continue
      if not(access(file,os.R_OK)):
        print('              is not readable')
        continue
      if file in files:
        print('              is already selected')
        continue
      nrf = not_readable(file)
      if len(nrf):
        if len(nrf) == 1 and nrf[0] == file:
          warn('file not readable')
        else:
          warn('files not readable:')
          for file in nrf: eprintf('  %s\n',file)
      else:
        if not match('-',file_id(file)):
          print('             ',mtime(file))
          print('             ',kMG(file_size([file])))
          if not file in files: files.append(file)
        print("           \r")

  if recipient == 'fex clipboard':
    recipient = '.'
    archive = 'STDFEX.tgz'
  elif recipient == 'fex archive':
    recipient = '_'
    archive = ask_archive(files)
    if archive is None: return
  elif len(files) == 1 and not path.isdir(files[0]):
    pass
  else:
    archive = ask_container(files)
    if archive is None: return

  if recipient == '.':
    comment = 'NOMAIL'
  else:
    while True:
      comment = inputline("Comment: ")
      if comment is None: return
      if comment == '?':
        print("Enter an optional comment to be sent in the notification email.")
      else:
        break

  # extra URI parameter in comment?
  comment = XUP(comment)

  # simulate CLI options
  if match('^:-',comment):
    # http://stackoverflow.com/questions/899276/python-how-to-parse-strings-to-look-like-sys-argv
    global maxtp,verbose
    maxtp = verbose = 0
    get_opt_arg("vdMC:c:X:m:",shlex.split(comment.strip(':')))
    comment = opts.get('C') or opts.get('c') or ''
    if 'd' in opts: delete = comment = 'DELETE'
    if 'v' in opts: verbose = opts['v']
    if 'm' in opts:
      try:    maxtp = int(opts['m'])
      except: maxtp = 0
    opts['-'] = ':'

  print()
  dir = getcwd()
  status = sendfile_retry(files,recipient,comment=comment)
  if archive: save_remove(archive)
  if status == 200: remember_recipient(recipient)
  if '-' in opts or 'X' in opts: wexit(status)
  chdir(dir)
  inputline('\nPress [ENTER] to continue')
  return status


def ask_container(files):
  archive = ''

  while not archive:
    try: archive = despace(inputline("Container name: "))
    except: return
    if archive == '?':
      print("To send more than one file we have to put them "
            "in a container archive.")
      print("Enter a name for this container. "
            "The recipient will see it in his download URL.")
      if len(files) == 1 and path.isdir(files[0]):
        print('Just press [ENTER] to use "%s" as the container name.' %
              files[0])
      print('[Ctrl]+[C] brings you back to the main menu.')
      archive = ''
      continue
    if archive == '.': archive = '_'
    if not match(r'[\w_]',archive): archive = ''
    if not archive and len(files) == 1 and path.isdir(files[0]):
      archive = path.basename(files[0])

  archive = subst(r'^\s*(.*?)\s*$',r'\1',archive)
  archive = subst(r'[\s\\/:]','_',archive)
  return archive


def ask_archive(files):

  while True:
    try: archive = despace(inputline("Archive name: "))
    except: return
    if archive == '?':
      print("Enter a name for this archive.")
      print('Just press [ENTER] to use "%s" as the archive name.' % archive)
      continue
    if not archive: archive = path.basename(files[0])
    if match(r'\w',archive): break

  archive = subst(r'^\s*(.*?)\s*$',r'\1',archive)
  archive = subst(r'[\s\\/:]','_',archive)
  return archive


def ask_recipient():
  global address

  read_addresses()
  if address:
    print('\nRecipients:\n')
    for (k,a) in sorted(address.items()):
      if not k in list(' x'): printf("[%s] %s\n",k,a)
    if user:
      address['X'] = 'fex clipboard'
      print('[X] fex clipboard')
#      address['A'] = 'fex archive'
#      print('[A] fex archive')
    if user and ' ' in address: printf("[SPACE] %s\n",address[' '])
    print("[ENTER] new address\n")
    sleep(1)
    while True:
      k = prompt_key("Select address key: [ ]\b\b")
      if k in list('\b\177\003\004'):
        print()
        return
      if k == '?':
        printf('\rYou must enter one of the [key] above')
        sleep(3)
        printf("\r                                     \r")
        continue
      if k == '\n' or k == '\r':
        printf("\r                                     \r")
        recipient = inputline("New recipient(s): ")
        if _m('^(.)$',recipient) and _1 in address:
          recipient = address[_1]
          print(recipient)
        break
      if k in address:
        recipient = address[k]
        print('%s] %s' % (k,recipient))
        break
      printf('\007unknown key]')
      sleep(1)

  else:
    recipient = inputline("Recipient(s): ")

  if (recipient is not None and 
      recipient != 'fex clipboard' and
      recipient != 'fex archive'):
    recipient = subst('[ ,;]+',',',despace(recipient.lower()))

  return recipient


def sendfile_retry(files,recipient,comment=''):
  global _
  global timeout
  global archive
  # global fileslist

  if _m('!(.+)',recipient):
    if not 'X' in opts: opts['X'] = subst('[!:]+','&',(_1))
    recipient = subst('!.*','',recipient)

  query_recipient = recipient
  if not (skey or gkey):
    if recipient == '_':
      query_recipient = user
    elif user == recipient or recipient == '.':
      query_recipient = user
      print('Recipient:',user)
    else:
      http_connect(server,port)
      if not sock: return
      query_sid()
      recipients = check_recipient(recipient)
      if recipients:
        query_recipient = recipients[0]
        for r in recipients: print('Recipient:',r)
      else:
        return 2

  #try:
  #  comment = comment.encode('utf8')
  #except UnicodeDecodeError:
  #  comment = comment.decode('iso-8859-1').encode('utf8')

  if not comment and recipient == '.': comment = 'NOMAIL'

  if not match(r'[\w_]',archive):
    if len(files) == 1:
      if path.isdir(files[0]) or recipient == '_':
        archive = path.basename(files[0])
    else:
      archive = ask_container(files)
      if not archive: return

  if recipient == '_':
    if match(r'\.tar$',archive):
      archive = subst(r'\.tar$','',archive)
      archive = archive+versiondate(files)+'.tar'
    elif match(r'\.tgz$',archive):
      archive = subst(r'\.tgz$','',archive)
      archive = archive+versiondate(files)+'.tgz'
    else:
      archive = subst(r'\.(zip|7z|rar)$','',archive)
      archive = archive+versiondate(files)+'.zip'

  if archive:
    archive = subst(r'[^\w\-+_=.]','_',archive)
    archive = subst(r'^\.','_',archive)
    nrf = not_readable(files)
    if len(nrf):
      warn('files not readable:')
      for file in nrf: eprintf('  %s\n',file)
      return
    fid = file_id(files)
    print("           \r")
    if match('-',fid): return
    size = file_size(files)

    if len(files) == 1:
      if _m(r'(.+[\\/])(.+)',files[0]):
        bdir = _1
        files = [_2]
        try:
          chdir(bdir)
        except (IOError,OSError) as e:
          warn('cannot chdir "%s" - %s' % (bdir,e.strerror))
          return
        print('%s:' % getcwd())
    else:
      drive = ''
      if _m(r'^(.:\\)',files[0]):
        drive = _1
        for file in files:
          if file[:3] != drive:
            drive = ''
            break
      # print("### drive=%s" % drive)
      bdir = path.dirname(path.dirname(files[0]))
      ### print("### [%s]" % bdir)
      if bdir and path.isdir(bdir):
        for file in files:
          if bdir != file[:len(bdir)]:
            bdir = ''
            break
        if bdir:
          try:
            # print('### cd "%s"' % bdir)
            chdir(bdir)
          except (IOError,OSError) as e:
            warn('cannot chdir "%s" - %s' % (bdir,e.strerror))
            return
          print('%s:' % getcwd())
          # files = [ subst(r'^[\\/]','',file[len(bdir):]) for file in files ]
          for (i,file) in enumerate(files):
            file = file[len(bdir):]
            file = subst(r'^[\\/]','',file)
            # print('### %s ###' % file)
            files[i] = file

    if _m(r'\.(7z|rar)$',archive):
      warn(_1+' container is not suported')
      return

    if match(r'\.(tar|tgz|zip)$',archive):
      archive = path.join(tmpdir,archive)
    elif size < 2**31:
      archive = path.join(tmpdir,archive+'.zip')
    else:
      archive = path.join(tmpdir,archive+'.tar')

    print()
    if verbose: print("creating",archive)

    if _m(r'\.(tar|tgz)$',archive):
      try:
        if _1 == 'tar':
          ao = tarfile.open(archive,'w')
        else:
          ao = tarfile.open(archive,'w:gz')
        for file in files:
          ao.add(file,recursive=True,filter=tar_report)
        ao.close()
      except:
        save_remove(archive)
        warn(sys.exc_info()[1])
        return
    elif match(r'\.zip$',archive):
      try:
        ao = ZipFile(archive,'w',compression=ZIP_DEFLATED)
        for file in files:
          if path.isdir(file):
            fps = []
            for (dirname,subdirs,filenames) in walk(file):
              if not match(r'[/\\]\.snapshot$',dirname):
                for filename in filenames:
                  fps.append(path.join(dirname,filename))
            for fp in sorted(fps,key=lambda s: s.lower()):
              print('zip "%s"' % fp)
              try:
                ao.write(fp)
              except:
                save_remove(archive)
                warn(sys.exc_info()[1])
                return
          else:
            print('zip "%s"' % file)
            try:
              ao.write(file)
            except:
              save_remove(archive)
              warn(sys.exc_info()[1])
              return
        ao.close()
      except:
        save_remove(archive)
        warn(sys.exc_info()[1])
        return
    else:
      die("unknown archive format "+archive)

    #fileslist = subst('.(tar|7z|zip)$','',path.join(tmpdir,archive))
    #fileslist += '.list'
    #try:
    #  flo = open(fileslist,'wb')
    #  for file in files: print(file.encode('utf8'),file=flo)
    #  flo.close()
    #except (IOError,OSError) as e:
    #  die('cannot write "%s" - %s' % (fileslist,e.strerror))
    #if match(r'\.tgz$',archive):
    #  warn('tgz container is not suported')
    #  return
    #elif match(r'\.tar$',archive):
    #  archive = path.join(tmpdir,archive)
    #  cmd = [sz,'a','-ttar',archive,'@'+fileslist]
    #elif match(r'\.zip$',archive):
    #  archive = path.join(tmpdir,archive)
    #  cmd = [sz,'a','-tzip',archive,'@'+fileslist]
    #elif match(r'\.7z$',archive):
    #  archive = path.join(tmpdir,archive)
    #  cmd = [sz,'a','-t7z',archive,'@'+fileslist]
    #elif size < 2**31:
    #  archive = path.join(tmpdir,archive+'.zip')
    #  cmd = [sz,'a','-tzip',archive,'@'+fileslist]
    #else:
    #  archive = path.join(tmpdir,archive+'.tar')
    #  cmd = [sz,'a','-ttar',archive,'@'+fileslist]
    #if verbose: print(cmd)
    #status = -1
    #try:
    #  status = subprocess.call(cmd)
    #except KeyboardInterrupt:
    #  eprintf("\n*interrupted*")
    #  sleep(1)
    #  return
    #except (IOError,OSError) as e:
    #  warn(cmd)
    #  warn('7z failed - %s' % e.strerror)
    #  return
    #if status:
    #  warn(cmd)
    #  warn('7z failed')
    #  return

    print()
    files = [archive]

  while True:

    file = files[0]

    if delete:
      fileo = None
      filesize = fid = 0
    else:
      if not path.exists(file):
        warn('"%s" does not exist' % file)
        return
      if not path.isfile(file):
        warn('"%s" is not a regular file' % file)
        return
      try:
        fileo = open(file,'rb')
        filesize = path.getsize(file)
      except (IOError,OSError) as e:
        eprintf('cannot open "%s" - %s',file,e.strerror)
        return
      except:
        e = sys.exc_info()[1]
        warn('cannot open "%s" - %s' % (file,e))
        return

      if not archive: 
        fid = file_id(file)
        print("           \r")
      if not fid or match('-',fid):
        warn('cannot determine file ID')
        return  #  else int(time.time())

    if match(r'[\\/]STDFEX\.tgz$',file): file = 'STDFEX'

    try:
      http_connect(server,port)
      if not sock: return
      query_sid()

      if overwrite or delete:
        seek = 0
      else:
        (seek,location) = query_file(user,query_recipient,file,fid)
        if (seek == filesize):
          eprintf('%s: has been already transferred\n',file)
          if query_recipient == user: print('Location:',location)
          return 0

      if seek:
        if False and archive:
          eprintf('%s: fast forward to byte %d (resuming)\n',file,seek)
          read_ahead(fileo,seek)
        else:
          eprintf('%s: resuming at byte %d\n',file,seek)
          fileo.seek(seek)

      status = sendfile(file,fileo,filesize,fid,seek,recipient,comment)
      if delete:
        if status == 200:
          print('"%s" deleted' % file)
        else:
          print('"%s" not deleted' % file)
      if archive: save_remove(archive)
      return status

    except socket.timeout:
      print("\ntimeout!")
      for w in range(timeout,0,-1):
        printf("retrying after %d seconds...\r",w)
        sleep(1)
      print("\n")


def sendfile(file,fileo,filesize,fid,seek,recipient,comment=''):
  global _

  signal.signal(signal.SIGINT,sigint_handler)
  reply = formdata_post(recipient,file,fileo,filesize,seek,fid,comment)
  if fileo: fileo.close()
  signal.signal(signal.SIGINT,signal.SIG_DFL)

  if len(reply) == 0: die("no response from %s:%s" % (server,port))
  _  = reply.pop(0)
  if _m('^HTTP.* 200 '):
    for _ in reply:
      if opts.get('X') and _m('X-(Recipient: .+)'): print(_1)
      if recipient == user or recipient == '.' or recipient == '_':
        if _m('X-(Location: .+)'):
          print(_1)
          if GUI:
            _ = _s('.*Location: ','')
            x = Tk()
            x.withdraw()
            x.clipboard_clear()
            x.clipboard_append(_)
            x.destroy()
    return 200
  else:
    return check_response(_,reply)


def formdata_post(recipient,
                  file=None,
                  fileo=None,
                  filesize=0,
                  seek=0,
                  fileid='',
                  comment='',
                  command=''):

  post = {
    'from': user,
    'to': recipient,
    'id': sid,
    'comment': comment,
    'command': command,
  }

  def timeout_handler(sig,frame): raise ValueError("timeout!")

  hh = []  # HTTP header
  hb = []  # HTTP body
  connection = ''
  boundary = rand_string(48)

  if file:
    if recipient == '_' : 
      post['to'] = '.'
      post['keep'] = '999'
    filename = path.basename(file)
    post['fileid'] = fileid
    post['filesize'] = str(filesize)
    if keep: post['keep'] = str(keep)
    if seek: post['seek'] = str(seek)
    fpsize = filesize - seek
  else:
    file = filename = ''
    fpsize = 0

  if skey:
    pv = 'from to skey keep autodelete comment seek filesize'
    post['skey'] = sid
    post['from'] = 'SUBUSER'
    post['to'] = '_'
  elif gkey:
    pv = 'from to gkey keep autodelete comment seek filesize'
    post['gkey'] = sid
    post['from'] = 'GROUPMEMBER'
    post['to'] = '_'
  elif recipient == 'nettest':
    pv = 'from to id comment command filesize'
    post['from'] = post['to'] = post['id'] = 'nettest'
  else:
    pv = 'from to id replyto keep autodelete comment command seek filesize'
    
  for v in pv.split():
    if v in post and len(post[v]):
      hb.append('--'+boundary)
      hb.append('Content-Disposition: form-data; name="%s"' % v.upper())
      hb.append('')
      hb.append(post[v])

  if file:
    hb.append('--'+boundary)
    hb.append('Content-Disposition: form-data; name="FILE"; filename="%s"' % filename)
    if not 'd' in opts:
      if 'M' in opts:
        hb.append('Content-Type: application/x-mime')
      else:
        hb.append('Content-Type: application/octet-stream')
      hb.append('Content-Length: %d' % fpsize)
      hb.append('X-File-ID: %s' % fileid)
      hb.append('')
    hb.append('')
    hb.append('--'+boundary+'--')
    # prevent proxy chunked mode reply
    connection = 'close'

    if fpsize < 0:
      length = fpsize
    else:
      length = 0
      for line in hb: length += len(line)+2
      length += fpsize

    if not 'd' in opts: hb[-2] = '(file content)'

  else:
    hb.append('--'+boundary+'--')
    length = len(''.join(hb))+len(hb)*2

  # extra URI parameter
  parameter = ''
  opt_X = opts.get('X')
  if opt_X and opt_X != '?': parameter = '?'+opt_X

  hh.append("POST %s/fup%s HTTP/1.1" % (proxy_prefix,parameter))
  hh.append("Host: %s:%d" % (server,port))
  hh.append("User-Agent: %s" % useragent)
  hh.append("Content-Length: %d" % length)
  hh.append("Content-Type: multipart/form-data; boundary=%s" % boundary)
  if connection: hh.append("Connection: %s" % connection)
  hh.append('')

  if file and not 'd' in opts:
    hb.pop()
    hb.pop()
    for line in hh: nvt_send(line)
    for line in hb: nvt_send(line)

    bs = kB64
    t0 = t2 = int(time())
    tt = t0-1
    t1 = 0
    tc = 0
    bytes = 0
    bt = 0
    pct = ''

    # for nettest
    if fileo is None: chunk = '#' * bs

    sock.settimeout(timeout)

    while True:
      if fileo is None:
        b = bs
        bytes += bs
      else:
        try:
          chunk = fileo.read(bs)
        except:
          die("cannot read from "+file)
        b = len(chunk)
        bytes += b
        if filesize > 0 and bytes+seek > filesize:
          die('"file" has grown while uploading')
      try:
        sock.sendall(chunk)
      except socket.error as e:
        die("cannot send to %s:%d - %s" % (server,port,e.strerror))
      bt += b
      t2 = time()
      if int(t2) > t1:
        # smaller block size is better on slow links
        if t1 and bs > kB4 and bytes/(t2-t0) < kB64: bs = kB4
        if filesize > 0:
          pct = "(%d%%)" % int((bytes+seek)*100.0/filesize)
          eprintf("%s: %d MB of %d MB %s %d kB/s\r",
              filename,
              int((bytes+seek)/MB),
              int(filesize/MB),
              pct,
              int(bt/kB/(t2-tt)))
        t1 = t2
        # time window for transfer rate calculation
        if t2-tt>10:
          bt = 0
          tt = t2
      if filesize > 0 and bytes >= fpsize: break
      while maxtp and bytes/kB/(time()-t0) > maxtp: sleep(1)

    send('\r\n--'+boundary+'--\r\n')

    if bytes+seek < filesize: die('"%s" has shrunk while uploading' % file)

    tt = t2-t0 or 1

    eprintf("%s: %d MB in %d s = %d kB/s        \n",
            filename,filesize/MB,tt,int(bytes/kB/tt))

  else:
    for line in hh: nvt_send(line)
    for line in hb: nvt_send(line)

  reply = []

  # beware: reads only HTTP header response!
  while nvt_get(): reply.append(_)

  return reply


def check_recipient(recipient):
  global _

  recipients = []
  reply = formdata_post(recipient,command='CHECKRECIPIENT')
  if len(reply) == 0: die("no response from %s:%s" % (server,port))
  _  = reply.pop(0)
  if not _m(r'^HTTP.* \d\d\d '):
    die("no F*EX server at %s:%s, response:\n%s" % (server,port,_))
  if _m(r'^HTTP.* (2\d\d) '):
    rc = _1
    for _ in reply:
      if _m(r'X-Recipient: (\S+) '): recipients.append(_1)
    return recipients
  elif _s('^HTTP.* 666 Bad Request - ',''):
    warn('bad server response: '+_)
    return
  else:
    check_response(_,reply)
    return


def query_sid():
  global sid,features,timeout

  sid = aid

  if port == 443 or proxy:
    if features: return # early return if we know enough
    req = "HEAD /index.html HTTP/1.1"
  else:
    req = "GET /SID HTTP/1.1"

  reply,header,body = http_request(req,server,port)
  # pp(header)
  # print()
  # pp(body)
  if not reply: die("no response from %s:%s" % (server,port))
  if (match('^HTTP.* [25]0[01] ',reply)):
    if not proxy and port != 443 and _m('^HTTP.* 201 (.+)',reply):
      sid = 'MD5H:'+md5h(aid+_1)
    for h in header:
      if _m(r'^X-Features: (.+)',h): features = _1
      if _m(r'^X-Timeout: (\d+)',h): timeout  = int(_1)


def check_response(reply,header):
  if not reply:
    eprintf("no response from %s:%s",server,port)
    return
  if _m(r'^HTTP/[\d.]+ (\d+) (.+)',reply):
    status = _1
    msg = _2
  else:
    eprintf("no F*EX server at %s:%s, response:\n%s",server,port,reply)
    return 0
  if match('^2',status):
    return int(status)
  if match('^5',status):
    eprintf("server error: %s\n%s\n",reply,'\n'.join(header))
    return int(status)
  for h in header:
    if match('^Location',h): msg += '\n'+h
  warn('server error: '+msg)
  return int(status)


def query_file(user,recipient,file,fid):
  global sid,features
  global _

  recipient = subst('[:,].*','',recipient)
  qfile = url_encode(path.basename(file))

  head = "HEAD %s/fop" % proxy_prefix
  if skey:
    user = 'SUBUSER'
    head += "/_/%s/%s??SKEY=%s" % (user,qfile,sid)
  elif gkey:
    user = 'GROUPMEMBER'
    head += "/_/%s/%s??GKEY=%s" % (user,qfile,sid)
  else:
    head += "/%s/%s/%s??ID=%s" % (recipient,user,qfile,sid)
  head += " HTTP/1.1"

  reply,header,body = http_request(head,server,port)
  if not reply: die("no response from %s:%d" % (server,port))

  if not match('^HTTP.* 200',reply):
    if grep('^(Server: fexsrv|X-Features:)',header):
      die("server response: "+subst(r'HTTP/[\d\. ]+','',reply))
    else:
      die("no fexserver at %s:%d" % (server,port))

  seek = 0
  qfid = features = location = cc = ''
  for _ in header:
    if   _m(r'^Content-Length:\s+(\d+)'): seek = int(_1)
    elif _m(r'^X-File-ID:\s+(.+)'):	  qfid = _1
    elif _m(r'^X-Features:\s+(.+)'):	  features = _1
    elif _m(r'^X-Location:\s+(.+)'):	  location = _1
    elif _m(r'^Connection: close'):	  cc = _

  # return true seek only if file is identified
  if qfid != fid: seek = 0

  # reconnect after connection close (proxy?!)
  if cc:
    http_connect(server,port)
    if not sock: return
    sid = aid

  return seek,location


def query_address_book():
  ab = {}
  req = "GET %s/fop/%s/%s/ADDRESS_BOOK?ID=%s HTTP/1.1" % \
        (proxy_prefix,user,user,sid)
  reply,header,body = http_request(req,server,port)
  for line in body.split('\n'):
    if _m(r'^\s*([\w+._-]+)\s+(\S+)',line): ab[_1] = _2
  return ab


def xx_send(files):
  global archive

  for file in files:
    if not path.exists(file):    die('"%s" does not exist' % file)
    if not access(file,os.R_OK): die('"%s" is not readable' % file)
  archive = 'STDFEX.tgz'
  status = sendfile_retry(files,user,'NOMAIL')
  if status is None: status = 99
  if status == 0:    status = 9
  if status == 200:  status = 0
  return status


def xx_get(edir=None):
  try:
    fex = fexget('STDFEX')
  except KeyboardInterrupt:
    eprintf("\n*interrupted*\n")
    os._exit(99)
  if fex is None: return 99
  if type(fex) is int: return fex
  if not tarfile.is_tarfile(fex):
    warn('%s is not a tar file' % fex)
    return 3
  try:
    fexo = tarfile.open(fex,'r:gz')
    print("\nFiles in transfer-container:\n")
    fexo.list()
  except tarfile.TarError:
    die('cannot read "%s"' % fex)
  printf("\nExtract these files? [Yn] ")
  k = get_key()
  if k in list('yY\n\r'):
    print('y')
    if edir is None:
      print()
      if GUI:
        printf('Extraction directory: ')
        Tk().withdraw()
        edir = askdirectory(title='select a directory',initialdir=HOME) or ''
        if windoof: edir = subst('/',r'\\',edir)
        set_window_focus()
        print(edir)
      else:
        edir = inputline("Extraction directory: ")
    if edir is None or edir == '': return
    if not path.isdir(edir):
      print("is not a directory!")
      sleep(3)
      return
    print()
    fexo.extractall(members=itar(fexo),path=edir)
    print()
    if windoof and edir != '.':
      print('explorer "%s"' % edir)
      subprocess.call(['explorer',edir])
  else:
    print('n')
  fexo.close()
  remove(fex)
  return 0


def manage_archives():
  '''
F*EX archives are tar or zip container files which are fexed to yourself.
They are versioned and have maximum expiration date.
You can exchange these archive files with all your other accounts on any host
using fexit or fexpush&fexpull or you can give their URLs to other users.
  '''
  (urls,comments,mbs) = get_archive_list()
  while True:
    cls()
    print('Archive files of')
    print('%s/%s' % (fexurl,user))
    print(manage_archives.__doc__)
    if urls:
      print('-'*78)
      n = 0
      for url in urls:
        n += 1
        comment = comments[url]
        mb = mbs[url]
        if comment: comment = '"%s"' % comment
        if _m(r'.*/(.+)_(\d+_\d+)\.(tar|tgz|zip)$',url):
          print('%3d %s %7d MB %s %s' % (n,_2,mb,_1,comment))
      print('-'*78)
      print()
    if 1:    print("key          action")
    if urls: print("[g]          get archive (download)")
    if 1:    print("[s]          save archive (upload)")
    if urls: print("[d]          delete archive")
    if urls: print("[w]          show archive in webbrowser")
    if urls: print("[u]          show archive URLs")
    if 1:    print("[BACKSPACE]  back to main menu")
    k = prompt_key("Select action key: [ ]\b\b")
    if k in list('r\b\177\003\004'): return
    elif k == 'g': pass
    elif k == 'd': pass
    elif k == 'w': pass
    elif k == '\r' or k == '\n':
      cls()
      sleep(1)
      (urls,comments,mbs) = get_archive_list()
      continue
    elif k == 's':
      print(k)
      sleep(1)
      ask_file('fex archive')
      (urls,comments,mbs) = get_archive_list()
      continue
    elif k == 'u':
      print(k)
      print()
      for url in urls: print(url)
      print()
      inputline('Press [ENTER] to continue')
      continue
    else:
      printf('\007unknown key]')
      sleep(1)
      continue
    
    print(k)
    n = inputline('Enter archive number: ')
    if not n: continue
    if n > '0' and match(r'^\d+$',n):
      n = int(n)-1
      try:
        url = urls[n]
      except:
        printf('Number out of range')
        sleep(2)
        continue
    else:
      printf('Is not a number!')
      sleep(2)
      continue
    print()
    
    if k == 'g':
      afile,archive,container = _m(r'.*/((.*)\.(tar|tgz|zip))',url)
      if ddir: 
        adir = path.join(ddir,archive)
        afile = path.abspath(path.join(ddir,afile))
        try:
          chdir(ddir)
        except (IOError,OSError) as e:
          warn('cannot chdir "%s" - %s' % (ddir,e.strerror))
          sleep(2)
          continue
      else:
        adir = path.join('.',archive)
        afile = path.abspath(afile)
      if path.exists(afile): remove(afile)
      try:
        status = fexget(url)
      except KeyboardInterrupt:
        eprintf("\n*interrupted*\n")
        sleep(1)
      if type(status) is not str:
        inputline('\nPress [ENTER] to continue')
        continue
      tmkdir(adir)
      try:
        chdir(adir)
      except (IOError,OSError) as e:
        warn('cannot chdir "%s" - %s' % (adir,e.strerror))
        sleep(2)
        continue
      print("Extracting to "+adir)
      if container == 'tar' or container == 'tgz':
        to = tarfile.open(afile)
        to.extractall()
        to.close()
      else:
        zo = ZipFile(afile,'r')
        zo.extractall()
        zo.close()
      chdir('..')
      remove(afile)
      if windoof:
        subprocess.call(['explorer',adir])
      
    if k == 'd':
      http_connect(server,port)
      if not sock: continue
      uri = re.search('(/fop/.*)',url).group(1)
      if sock:
        reply,header,body = http_request(
          "GET %s/%s?DELETE HTTP/1.0" % (proxy_prefix,uri),
          server,port
        )
        if not reply:
          warn('no F*EX server at %s:%d' % (server,port))
        elif match('^HTTP.* 200',reply):
          print('%s deleted' % url)
        else:
          print('Bad server reply: %s' % reply)
        (urls,comments,mbs) = get_archive_list()
      
    if k == 'u':
      print(url)
      
    if k == 'w':
      if windoof:
        syscall('start','',url)
      else:
        system('xdg-open %s || firefox %s' % (url,url))
      sleep(2)
    
    inputline('\nPress [ENTER] to continue')

      
def get_archive_list():
  global _
  urls = []
  comments = {}
  mbs = {}
  fuser = ''

  http_connect(server,port)
  if not sock: return
  query_sid()
  reply = formdata_post(user,command='LIST')
  if len(reply) == 0: die("no response from %s:%s" % (server,port))
  _  = reply.pop(0)
  if _m('^HTTP.* 200 '):
    # for line in reply: print(line)
    while nvt_get() is not None:
      if _m(r'^Files for (\S+)'):
        fuser = 'from %s :' % _1
        continue
      if _ == fuser:
        while nvt_get() is not None:
          if _m('^ *$'):
            while nvt_get() is not None: pass
            break
          if _m(r'(\d+) MB .*<a href="(http.*?/fop/\w+/(.*_\d{8}_\d{6}\.(tar|tgz|zip)))".*"(.*)"'):
            mb = _1
            url = _2
            comment = _5
            if comment == 'NOMAIL': comment = '';
            urls.append(url)
            mbs[url] = int(mb)
            comments[url] = comment
  else:
    check_response(_,reply)

  sock.close()
  return urls,comments,mbs


def sex_send(files):
  bs = kB64

  for file in files:
    if not path.exists(file):    die('"%s" does not exist' % file)
    if not access(file,os.R_OK): die('"%s" is not readable' % file)

  signal.signal(signal.SIGINT,sigint_handler)

  http_connect(server,port)
  if not sock: return
  print("connected to %s:%d, waiting for peer..." % (server,port))
  # sock.setblocking(1)
  sfo = sock.makefile('w',bs)
  taro = tarfile.open(fileobj=sfo,mode='w|')

  try:

    reply,header,body = http_request(
      "POST /sex?BS=%d&user=%s&stream=xx HTTP/1.0" % (bs,user),
      server,port
    )

    if not match('^HTTP/1.9 199',reply):
      warn('no SEX server at %s:%d' % (server,port))
      return
    if not match('^HTTP/1.. 200',header[0]):
      warn('SEX server %s:%d not ready' % (server,port))
      return

    for file in files:
      try:
        taro.add(file,recursive=True,filter=tar_report)
      except socket.error as e:
        warn(e.strerror)
        return

  except KeyboardInterrupt:
    eprintf("\n*interrupted*\n")
    return

  taro.close()
  sfo.close()
  sock.close()

  return 0


def sex_get(edir=None):
  bs = kB64

  signal.signal(signal.SIGINT,sigint_handler)

  if edir is None:
    print()
    if GUI:
      printf('Extraction directory: ')
      Tk().withdraw()
      edir = askdirectory(title='select a directory',initialdir=HOME) or ''
      if windoof: edir = subst('/',r'\\',edir)
      set_window_focus()
      print(edir)
    else:
      edir = inputline("Extraction directory: ")
  if edir is None or edir == '': return
  if not path.exists(edir):    die('"%s" does not exist' % file)
  if not access(edir,os.W_OK): die('"%s" is not writable' % file)
  if not path.isdir(edir):     die('"%s" is not a directory' % file)

  http_connect(server,port)
  if not sock: return
  query_sid()
  reply,header,body = http_request(
    "GET /sex?BS=%d&user=%s&ID=%s&stream=xx HTTP/1.0" % (bs,user,sid),
    server,port
  )
  if match('^HTTP/1.. 503',reply):
    warn('no stream at %s:%d' % (server,port))
    return
  if not match('^HTTP/1.. 200',reply):
    warn('bad reply from %s:%d : %s' % (server,port,reply))
    return

  sfo = sock.makefile('r',bs)
  taro = tarfile.open(fileobj=sfo,mode='r|')

  try:
    taro.extractall(members=itar(taro),path=edir)
    #for ti in taro:
    #  print('untar "%s"' % ti.name)
    #  taro.extract(ti)
  except tarfile.ReadError as e:
    die(e)
  except KeyboardInterrupt:
    eprintf("\n*interrupted*\n")
    return

  return 0


def fexget(url,notest=''):
  '''on success return download-file, else None or HTTP status'''
  global _
  global server,port,user

  if windoof and match('^http',url) and not path.exists(fddir):
    cmd = ['mklink','/d',fddir,ddir]
    # print(cmd)
    try: subprocess.call(cmd)
    except: pass

  if verbose: print(getcwd())

  if _m(r'https://(.+)(/fop/.+)',url):
    server = _1
    port = 443
    fop = _2
  elif _m(r'http://(.+):(\d+)(/fop/.+)',url):
    server = _1
    port = int(_2)
    fop = _3
  elif _m(r'http://(.+)(/fop/.+)',url):
    server = _1
    port = 80
    fop = _2
  elif url == 'STDFEX':
    file = url
  else:
    warn('"%s" is not a F*EX download URL' % url)
    return

  try:
    http_connect(server,port)
  except socket.error as e:
    warn("cannot connect to %s:%d - %s\n",server,port,e.strerror)
    return
  if not sock: return

  if url == 'STDFEX':
    query_sid()
    fop = "/fop/%s/%s/STDFEX?ID=%s" % (user,user,sid)
    download = path.join(tmpdir,url)
    notest = url
    seek = 0
  else:
    reply,header,body = http_request(
      "HEAD %s%s  HTTP/1.0" % (proxy_prefix,fop),
      server,port
    )
    if not reply or not match('^HTTP/',reply):
      warn('no F*EX server at %s:%d' % (server,port))
      return
    if not match(r'^HTTP/[\d.]+ 200',reply):
      warn('file not found on server')
      if _m(r'^HTTP/[\d.]+ (\d+)',reply): return int(_1)
      else:                               return 666
    file = path.basename(fop)
    size = 0
    for _ in header:
      if _m(r'(?i)^Content-Disposition: attachment; filename="(.+)"'):
        file = _1
      if _m(r'(?i)^Content-Length: (\d+)'):
        size = int(_1)

    if not size:
      warnw('file size unknown')
      return

    if path.exists(file) and not overwrite:
      warnw('destination file "%s" does already exist' % file)
      return

    download = file+'.tmp'
    try:
      seek = path.getsize(download)
    except:
      seek = 0

  if not notest:
    test = file+'.test'
    try:
      testo = open(test,'wb')
    except (IOError,OSError) as e:
      die('cannot write %s - %s' % (test,e.strerror))
    t0 = t1 = t2 = int(time())
    n = 0
    buf = b'.' * MB
    wse('checking storage...\r')
    while path.getsize(test)+seek < size:
      try:
        testo.write(buf)
      except (IOError,OSError) as e:
        remove(test)
        die('cannot write %s - %s' % (test,e.strerror))
      n += 1
      t2 = int(time())
      if t2 > t1:
        wse('checking storage... %d MB\r' % n)
        t1 = t2
    testo.close()
    wse('checking storage... %d MB ok!\n' % n)
    remove(test)
    try:
      http_connect(server,port)
    except socket.error as e:
      warn("cannot connect to %s:%d - %s\n",server,port,e.strerror)
      return
    if not sock: return

  dkey = extract(r'/fop/(\w+)/',fop)

  nvt_send("GET %s%s HTTP/1.1" % (proxy_prefix,fop))
  nvt_send("Host: %s:%d" % (server,port))
  nvt_send("User-Agent: "+useragent)
  nvt_send("Cookie: dkey="+dkey)
  nvt_send("Connection: close")
  if seek: nvt_send("Range: bytes=%d-" % seek)
  nvt_send('')
  header = []
  reply = nvt_get()
  if not reply or not match('^HTTP/',reply):
    warn('no F*EX server at %s:%d' % (server,port))
    return
  if seek and match(r'^HTTP/[\d.]+ 206',reply):
    pass
  elif not match(r'^HTTP/[\d.]+ 200',reply):
    warn('file not found on server')
    if _m(r'^HTTP/[\d.]+ (\d+)',reply): return int(_1)

  while True:
    line = nvt_get()
    if line is None:
      warn('interrupted reply from %s:%d' % (server,port))
      return
    if line == '': break
    header.append(line)

  cl = 0
  for _ in header:
    if url != 'STDFEX':
      if _m(r"X-Size:\s+(\d+)"):
        if int(_1) != size:
          warn('file size has changed')
          return
      if _m(r'(?i)^Content-Disposition: attachment; filename="(.+)"'):
        if _1 != file:
          warn('file name has changed')
          return
    if _m(r'(?i)^Content-Length: (\d+)'):
      cl = int(_1)

  if not cl:
    warnw('unknown Content-Length')
    return

  try:
    if seek:
      downloado = open(download,'ab')
    else:
      downloado = open(download,'wb')
  except (IOError,OSError) as e:
    die('cannot write %s - %s' % (download,e.strerror))

  t0 = t1 = t2 = int(time())
  tb = bt = B = 0
  bs = kB64
  if seek: eprintf("resuming at byte %d\n",seek)
  while B < cl:
    try:
      buf = sock.recv(bs)
    except socket.timeout:
      print("\ntimeout!")
      return fexget(url)
    except:
      print("\nnetwork read error")
      break
    b = len(buf)
    if not b: break
    downloado.write(buf)
    B += b
    tb += b
    bt += b
    t2 = time()
    if int(t2) > t1:
      kBs = int(bt/kB/(t2-t1))
      if kBs < 10: kBs = int(tb/kB/(t2-t0))
      t1 = t2
      bt = 0
      # smaller block size is better on slow links
      if bs > kB4 and tb/(t2-t0) < kB64: bs = kB4
      if tb < 10*MB:
        eprintf("%s: %d kB (%d%%) %d kB/s \r",
                download,
                int((tb+seek)/kB),
                int(100.0*(tb+seek)/(cl+seek)),
                kBs)
      else:
        eprintf("%s: %d MB (%d%%) %d kB/s        \r",
                download,
                int((tb+seek)/MB),
                int(100.0*(tb+seek)/(cl+seek)),
                kBs)
    if maxtp:
      if t2 == t0 and B > maxtp*kB:
        if verbose: printf("\nsleeping...\r")
        sleep(1)
      else:
        while t2 > t0 and tb/kB/(t2-t0) > maxtp:
          if verbose: printf("\nsleeping...\r")
          sleep(1)
          t2 = time()

  sock.close()
  downloado.close()

  if tb < cl:
    print()
    warn("%s annouced %d bytes, but only %d bytes has been read" %
         (server,cl,tb))
    for w in range(timeout,0,-1):
      printf("retrying after %d seconds...\r",w)
      sleep(1)
    print("\n")
    return fexget(url)

  tt = t2-t0
  tm = int(tt/60)
  ts = tt-tm*60
  kBs = int(tb/kB/(tt or 1))
  if seek:
    eprintf("%s: %d MB, last %d MB in %d s = %d kB/s      \n",
            file,int((tb+seek)/MB),int(tb/MB),tt,kBs)
  else:
    eprintf("%s: %d MB in %d s = %d kB/s      \n",
            file,int(tb/MB),tt,kBs)

  if overwrite and path.exists(file):
    try: remove(file)
    except: pass

  if url == 'STDFEX':
    return download
  else:
    try:
      rename(download,file)
    except (IOError,OSError) as e:
      warn('cannot rename "%s" to "%s" - %s' % (download,file,e.strerror))
      return
    return file


def fexdel(url):
  url += '?DELETE'
  req = urllib.Request(url)
  req.add_header('User-Agent',useragent)
  try:
    u = urllib.urlopen(req)
  except urllib.URLError as e:
    die('server reply: %s' % (e.reason))
  except urllib.HTTPError as e:
    die('bad server reply: %d %s' % (url,e.code,e.reason))
  except (IOError,httplib.BadStatusLine,httplib.HTTPException):
    die('connection reset by router or firewall')
  except socket.error as e:
    die('cannot connect - %s' % e)
  status = u.getcode()
  if status == 200:
    print('file deleted')
    return 0
  else:
    print('URL not valid')
    return status


def url_encode(s):
  if windoof:
    try:
      s = s.decode('latin-1').encode("utf-8")
    except:
      return subst(r'(?i)[^\d\-a-z_+.=]','_',s)

  u = ''
  for c in list(s):
    try:
      if match(r'[_=:,;<>()+.\w\-]',c):
        u += c
      else:
        u += "%{0:02x}".format(ord(c),"x").upper()
    except:
      u += '_'
  return u


def file_id(x):

  show_scanning()
  
  if type(x) is list:
    fid = ''
    for file in x: fid += file_id(file)
    if match('-',fid): return '-'
    else:              return md5h(fid)

  # for (dirname,subdirs,filenames) in walk(file):
  if not path.islink(x) and path.isdir(x):
    dir = x
    fid = ''
    try:
      for file in listdir(dir): 
        if file != '.snapshot': fid += file_id(path.join(dir,file))
    except OSError as e:
      warn('cannot read %s - %s' % (dir,e.strerror))
      return '-'
    if match('-',fid): return '-'
    else:              return md5h(fid)

  file = x
  if verbose: print(file)
  try:
    fs = lstat(file)
  except os.error as e:
    warn('cannot read %s - %s' % (file,e.strerror))
    return '-'

  return md5h("%s %d %d %d %d" %
              (file,fs.st_dev,fs.st_ino,fs.st_size,fs.st_mtime))


def file_size(x):

  if type(x) is list:
    size = 0
    for file in x: size += file_size(file)
    return size

  file = x

  if path.islink(file): return 0

  try:
    fs = stat(file)
  except os.error as e:
    warn('cannot read %s - %s' % (file,e.strerror))
    return 0

  if path.isdir(file):
    dir = file
    size = 0
    try:
      for file in listdir(dir): 
        if file != '.snapshot': size += file_size(path.join(dir,file))
    except OSError as e:
      warn('cannot read %s - %s' % (dir,e.strerror))
      return 0
    return size

  return fs.st_size


def not_readable(x):

  show_scanning()

  if type(x) is list:
    nrf = []
    for file in x: nrf.extend(not_readable(file))
    return nrf

  file = x
  if verbose: print(file)

  if path.islink(file): return []

  if not access(file,os.R_OK): return [file]

  if path.isdir(file):
    dir = file
    nrf = []
    try:
      for file in listdir(dir): 
        if file != '.snapshot':
          pfile = path.join(dir,file)
          if not path.islink(pfile): nrf.extend(not_readable(pfile))
    except OSError as e:
      return [dir]
    return nrf

  return []


def show_scanning():
  global sss
  
  if sss == 0:
    write("-\r")
    sss = 1
  elif sss == 1:
    write("\\\r")
    sss = 2
  elif sss == 2:
    write("|\r")
    sss = 3
  elif sss == 3:
    write("/\r")
    sss = 0


def tar_report(tarinfo):
  print('tar "%s"' % tarinfo.name)
  return tarinfo


def itar(tar):
  '''iterator for tar objects to extract'''
  for ti in tar:
    # minimal protection against dangerous file names
    # see http://bugs.python.org/issue21109#msg215656
    ti.name = subst(r'^(?i)([a-z]:)?(\.\.)?[/\\]','',ti.name)
    print('untar "%s"' % ti.name)
    yield ti


def rand_string(n):
  rc = string.ascii_letters+string.digits
  rn =len(rc)
  rs = ''
  for i in range(1,n+1):
    rs += rc[random.randint(0,rn-1)]
  return rs


def set_window_focus():
  if windoof:
    import ctypes
    kernel32 = ctypes.WinDLL('kernel32')
    user32 = ctypes.WinDLL('user32')
    hcon = kernel32.GetConsoleWindow()
    if hcon and user32.SetForegroundWindow(hcon):
      return True
    else:
      return False


def set_path(dir):
  cp = r'Software\Microsoft\Command Processor'
  wrar = get_winreg(cp,'AutoRun')
  ar = HOME + '\\autorun.cmd'
  setpath = 'set PATH=%PATH%;%USERPROFILE%\\Desktop'

  if wrar is None or wrar != ar:
    if verbose: print("writing cmd.exe AutoRun registry entry")
    set_winreg(cp,'AutoRun',ar)

  try:
    aro = open(ar,'r')
    while getline(aro) != None:
      if _.find(setpath) >= 0:
        aro.close()
        return
    aro.close()
  except:
    pass

  try:
    aro = open(ar,'a')
    if wrar and wrar != ar: aro.write('\r\n%s\r\n' % wrar)
    aro.write('\r\n%s\r\n' % setpath)
    aro.close()
    print('fexit PATH written to "%s"' % ar)
  except (IOError,OSError) as e:
    warn('cannot write to "%s" - %s' % (ar,e.strerror))

  inputline('Press [ENTER] to continue')


# http://stackoverflow.com/questions/15128225/python-script-to-read-and-write-a-path-to-registry
def get_winreg(key,subkey):
  try:
    rkey = winreg.OpenKey(winreg.HKEY_CURRENT_USER,key,0,winreg.KEY_READ)
    rvalue,rtype = winreg.QueryValueEx(rkey,subkey)
    winreg.CloseKey(rkey)
  except WindowsError:
    rvalue,rtype = None,None
  return rvalue


def set_winreg(key,subkey,value):
  winreg.CreateKey(winreg.HKEY_CURRENT_USER,key)
  rkey = winreg.OpenKey(winreg.HKEY_CURRENT_USER,key,0,winreg.KEY_WRITE)
  winreg.SetValueEx(rkey,subkey,0,winreg.REG_SZ,value)
  winreg.CloseKey(rkey)
  # except WindowsError:


def check_7z():
  global sz

  if windoof:
    sz = path.join(fexhome,'7za.exe')
    szurl = "http://fex.belwue.de/download/7za.exe"

    if not path.exists(sz) or path.getsize(sz) < 9999:
      try:
        szo = open(sz,'wb')
      except (IOError,OSError) as e:
        die('cannot write %s - %s' % (sz,e.strerror))
      printf("\ndownloading %s\n",szurl)
      try:
        req = urllib.Request(szurl)
        req.add_header('User-Agent',useragent)
        u = urllib.urlopen(req)
      except urllib.URLError as e:
        die('cannot get %s - %s' % (szurl,e.reason))
      except urllib.HTTPError as e:
        die('cannot get %s - server reply: %d %s' % (szurl,e.code,e.reason))
      except (IOError,httplib.BadStatusLine,httplib.HTTPException):
        die('cannot get %s - connection reset by router or firewall' % szurl)
      except socket.error as msg:
        die('cannot get %s - %s' % (szurl,msg))
      if u.getcode() == 200:
        copy_file_obj(u,szo)
        szo.close()
      else:
        die('cannot get %s - server reply: %d' % (szurl,u.getcode()))

  else:
    from distutils.spawn import find_executable
    sz = find_executable("7z") or find_executable("7za")
    if not sz: die("7z is not installed")


def update():

  print()

  if windoof:
    fexiturl = "http://fex.belwue.de/download/fexit.exe"
    new = subst(r'fexit(\.exe)?$','fexit_new.exe',prg)
    if new == prg:
      warnw("unknown program name "+prg)
      return
    try:
      newo = open(new,'wb')
    except (IOError,OSError) as e:
      warnw('cannot write %s - %s' % (new,e.strerror))
      return
    printf("\ndownloading %s\n",fexiturl)
    try:
      req = urllib.Request(fexiturl)
      req.add_header('User-Agent',useragent)
      u = urllib.urlopen(req)
    except urllib.URLError as e:
      warnw('cannot get %s - %s' % (fexiturl,e.reason))
      return
    except urllib.HTTPError as e:
      warnw('cannot get %s - server reply: %d %s' % (fexiturl,e.code,e.reason))
      return
    except (IOError,httplib.BadStatusLine,httplib.HTTPException):
      warnw('cannot get %s - connection reset by router or firewall' % fexiturl)
      return
    except socket.error as msg:
      warnw('cannot get %s - %s' % (fexiturl,msg))
      return
    if u.getcode() == 200:
      try:
        copy_file_obj(u,newo)
        newo.close()
      except (IOError,OSError) as e:
        warnw('cannot write "%s" - %s' % (new,e.strerror))
        return
    else:
      warnw('cannot get %s - server reply: %d' % (fexiturl,u.getcode()))
      return
    sleep(3)
    os.execl(new,new)
    wexit(1)

  else:
    print("function not available for UNIX")
    sleep(3)


def get_proxy():
  global proxy

  proxy = getenv('HTTP_PROXY')

  if not proxy and windoof:
    try:
       # http://stackoverflow.com/questions/6935796/which-python-module-to-use-to-access-the-proxy-setting-of-windows-7
      import _winreg
      proxy = _winreg.OpenKey(_winreg.HKEY_CURRENT_USER,
              r"Software\Microsoft\Windows\CurrentVersion\Internet Settings")
      server,x = _winreg.QueryValueEx(proxy,"ProxyServer")
      enabled,x = _winreg.QueryValueEx(proxy,"ProxyEnable")
      if enabled: proxy = server
      else:       proxy = ''
    except:
      proxy = ''

  if proxy:
    if match('https://',proxy):
      if _m(r':(\d+)',proxy):
        if _1 != '443': die('https proxy must use port 443')
      proxy = subst('https://','',proxy)
      if not match(':\d',proxy): proxy += ':443'
    else:
      proxy = subst('http://','',proxy)
      if not match(':\d',proxy): proxy += ':80'


def tmkdir(dir):
  if not path.isdir(dir):
    try:
      makedirs(dir)
    except (IOError,OSError) as e:
      die('cannot mkdir "%s" - %s' % (dir,e.strerror))


def get_sgkey(recipient):
  global skey,gkey,aid,sid,user

  if not match(',',recipient):
    if _m(r'skey=(\w+)',recipient): aid = skey = _1
    if _m(r'gkey=(\w+)',recipient): aid = gkey = _1


def b64e(s):
  return str(b64encode(s.encode('utf8')))


def utf8b(s):
  return s.encode('utf8')


### fpl ###

def inputline(prompt=''):
  global _

  _ = ''

  # https://docs.python.org/2/library/readline.html
  # http://stackoverflow.com/questions/6656819/filepath-autocompletion-using-users-input
  try:
    if python2: _ = raw_input(prompt)
    if python3: _ = input(prompt)
  except:
    print()
    return

  if _m("^'(.+)'$"): _ = _1
  if _m('^"(.+)"$'): _ = _1
  return _


# http://stackoverflow.com/questions/292095/polling-the-keyboard-in-python
def get_paste():
  while True:
    c = msvcrt.getwch()
    if c == '\t': return ''
    if c == '\003' or c == '\004': return None
    if not (c == '\n' or c == '\r'): break
  paste = c
  while msvcrt.kbhit():
    c = msvcrt.getwch()
    if c == '\n' or c == '\r': break
    paste += c
  if match(r'\s',paste) and _m('^"(.+)"$',paste): paste = _1
  return paste


def getline(fo):
  global _
  _ = fo.readline()
  if len(_):
    _ = _.rstrip('\n')
    _ = _.rstrip('\r')
    return _
  else:
    return None


def shcmd(cmd):
  if windoof:
    r = subprocess.check_output(cmd,universal_newlines=True)
  else:
    r = subprocess.check_output(cmd,shell=True)
  if python3: r = r.decode()
  if r.count("\n") == 1:
    return(subst(r"\n",'',r))
  else:
    return(r)


def mtime(file,format='%Y-%m-%d %H:%M:%S'):
  try:
    mt = lstat(file).st_mtime
  except:
    return None
  return strftime(format,localtime(mt))


def d3(s):
  s = str(s)
  while match(r'\d\d\d\d',s): s = subst(r'(\d)(\d\d\d)\b',r'\1,\2',s)
  return s


def d3b(B):
  if B > 999*GB: return d3(B/GB)+" GB"
  if B > 999*MB: return d3(B/MB)+" MB"
  if B > 999*kB: return d3(B/kB)+" kB"
  if B >= 0:     return d3(B)+" B"


def kMG(B):
  if B > 99*GB: return "%d GB" % (B/GB)
  if B > 99*MB: return "%d MB" % (B/MB)
  if B > 99*kB: return "%d kB" % (B/kB)
  if B >= 0:    return "%d B" % B


def extract(x,s=None,f=None):
  if s is None: s = _
  if f: m = re.search(x,s,flags=f)
  else: m = re.search(x,s)
  if m: return m.group(1)
  else: return ''


def _m(x,s=None,f=None):
  global _1,_2,_3,_4,_5,_6,_7,_8,_9
  _1 = _2 = _3 = _4 = _5 = _6 = _7 = _8 = _9 = None

  if s is None: s = _
  if f: m = re.search(x,s,flags=f)
  else: m = re.search(x,s)
  if m:
    match = []
    try:
      _1 = m.group(1); match.append(_1)
      _2 = m.group(2); match.append(_2)
      _3 = m.group(3); match.append(_3)
      _4 = m.group(4); match.append(_4)
      _5 = m.group(5); match.append(_5)
      _6 = m.group(6); match.append(_6)
      _7 = m.group(7); match.append(_7)
      _8 = m.group(8); match.append(_8)
      _9 = m.group(9); match.append(_9)
    except:
      pass
    if match: return match
    else:     return s
  else:
    return None


def _s(x,r,s=None,c=0,f=None):
  global _

  __ = z = s
  if s is None: s = _
  if _m(x,s,f):
    if f: z = re.sub(x,r,s,c,f)
    else: z = re.sub(x,r,s,c)
    if z != s:
      if __ is None: _ = z
      return z


def grep(pattern,strings):
  rx = re.compile(pattern)
  return [string for string in strings if rx.match(string)]


def read_ahead(pipe,seek):
  '''emulate seek on a pipe'''

  bs = kB64
  s = 0

  while s < seek:
    n = seek-s
    if n > bs: n = bs
    pipe.read(n)
    s += n


def get_opt_arg(opt,argv=None):
  global opts,args

  if argv is None:
    if windoof:
      argv = []
      for arg in sys.argv[1:]: argv += glob(arg) or [arg]
    else:
      argv = sys.argv[1:]

  try:
    optslist,args = getopt(argv,opt)
  except GetoptError as err:
    warn(str(err))
    show_usage(2)

  opts = {}
  for (o,a) in optslist:
    o = o[1]
    if o == "h":
      show_usage(0)
    elif opt.find(o+":") >= 0:
      opts[o] = a
    else:
      if o in opts: opts[o] += 1
      else:         opts[o] = 1


def XUP(comment):
  '''extract extra URI parameter in comment'''
  global opts

  if _m(r'^!(\S+)!',comment) and match(r'\w',_1):
    opts['X'] = subst(r'[ ,:!\?]+','&',despace(_1))
    comment = subst('^!\S+! *','',comment)

  return comment


def nettest(url,up,down):
  global aid,sid,user

  parse_url(url)
  nettest = aid = sid = 'nettest'

  if up:
    http_connect(server,port)
    if not sock:
      warn('cannot connect to %s:%d' % (server,port))
      return
    if not check_recipient(nettest):
      warn('nettest not available on %s' % fexurl)
      return
    print('fexit: upload to %s:%d' % (server,port))
    formdata_post(nettest,nettest,None,up*MB,comment='NOSTORE')

  if down:
    http_connect(server,port)
    if not sock: return
    print('fexit: download from %s:%d' % (server,port))
    nvt_send("GET %s/ddd/%s HTTP/1.0" % (proxy_prefix,down))
    nvt_send("Host: %s:%d" % (server,port))
    nvt_send("User-Agent: "+useragent)
    nvt_send('')
    reply = nvt_get()
    if not reply or not match('^HTTP/',reply):
      warn('no F*EX server at %s:%d' % (server,port))
      return
    elif not match(r'^HTTP/[\d.]+ 200',reply):
      warn('no nettest download service on %s' % fexurl)
      if _m(r'^HTTP/[\d.]+ (\d+)',reply): return int(_1)
      return

    while True:
      line = nvt_get()
      if line is None:
        warn('interrupted reply from %s:%d' % (server,port))
        return
      if line == '': break

    t0 = t1 = t2 = int(time())
    tb = bt = B = 0
    bs = kB64
    cl = down * MB
    while B < cl:
      try:
        buf = sock.recv(bs)
      except socket.timeout:
        warn("timeout")
        return
      except:
        warn("network read error")
        return
      b = len(buf)
      if not b: break
      B += b
      tb += b
      bt += b
      t2 = time()
      if int(t2) > t1:
        kBs = int(bt/kB/(t2-t1))
        if kBs < 10: kBs = int(tb/kB/(t2-t0))
        t1 = t2
        bt = 0
        # smaller block size is better on slow links
        if bs > kB4 and tb/(t2-t0) < kB64: bs = kB4
        if tb < 10*MB:
          eprintf("%s: %d kB (%d%%) %d kB/s \r",
                  nettest,int(tb/kB),int(100.0*tb/cl),kBs)
        else:
          eprintf("%s: %d MB (%d%%) %d kB/s        \r",
                  nettest,int(tb/MB),int(100.0*tb/cl),kBs)

    sock.close()

    tt = t2-t0
    tm = int(tt/60)
    ts = tt-tm*60
    kBs = int(tb/kB/(tt or 1))
    eprintf("%s: %d MB in %d s = %d kB/s        \n",
            nettest,int(tb/MB),tt,kBs)

  return 0


def versiondate(files):
  time = strftime('_%Y%m%d_%H%M%S',localtime(nmtime(files)))
  print("           \r")
  return time


def nmtime(files,nmt=0):
  for file in files:
    show_scanning()
    # for (dirname,subdirs,filenames) in walk(file):
    if path.isdir(file) and not path.islink(file):
      dir = file
      for dfile in listdir(dir):
        if dfile != '.snapshot':
          mt = nmtime([path.join(dir,dfile)],nmt)
          if mt and mt > nmt: nmt = mt
    else:
      try:
        mt = lstat(file).st_mtime
        if mt and mt > nmt: nmt = mt
      except: pass
  return nmt


def despace(s):
  return ' '.join(s.split())


def b64fix(s):
  while len(s) % 4: s += '='
  return s


def show_usage(status):
  global usage

  if status: print(usage,file=sys.stderr)
  else:      print(usage)
  os._exit(status)
  sys.exit(status)


def sigint_handler(sig,frame):
  print()
  die('*ABORTED*',99)


def cls():
  if windoof: syscall('cls')
  else:       syscall('clear')


def syscall(*cmd):
  if windoof: cmd = ['cmd','/d','/c']+list(cmd)
  if verbose: print(cmd)
  subprocess.call(cmd)


def strip(s):
  if python2:
    import string
    return string.strip(s)
  else:
    return s.strip()
  

def write(*objs):
  print(*objs,end='')
  sys.stdout.flush()
  # sys.stdout = fdopen(sys.stdout.fileno(), 'w', 0)


def printf(format,*args):
  sys.stdout.write(format % args)
  sys.stdout.flush()


def eprintf(format,*args):
  sys.stderr.write(format % args)
  sys.stderr.flush()


def warn(*objs):
  print('Warning: ',file=sys.stderr,end='')
  if objs:
    print(*objs,file=sys.stderr)
  else:
    line = currentframe().f_back.f_lineno
    print('line '+str(line),file=sys.stderr)


def warnw(*objs):
  warn(*objs)
  inputline('Press [ENTER] to continue')


def wse(*objs):
  print(*objs,file=sys.stderr,end='')


def debug(s):
  from inspect import currentframe
  line = currentframe().f_back.f_lineno
  print("DEBUG %d: %s" % (line,s))


def die(msg='',status=1):
  if not msg:
    line = currentframe().f_back.f_lineno
    msg = 'line '+str(line)

  eprintf("%s: %s\n",prg,msg)

  try:
    if archive: save_remove(archive)
  except:
    pass

  wexit(status)


def save_remove(*files):
  for file in files:
    try:
      if file.find(tmpdir) == 0: remove(file)
    except:
      pass


def copy_file_obj(fsrc,fdst,length=kB64):
  '''copy data from file-like object fsrc to file-like object fdst'''
  while True:
    buf = fsrc.read(length)
    if not buf: break
    fdst.write(buf)


def wexit(status):
  if archive: save_remove(archive)
  if windoof and not opts and not arecipient:
    inputline('\npress [ENTER] to exit')
  if status is None: status = 2
  os._exit(status)
  sys.exit(status)


match = re.search
subst = re.sub

try:
  wexit(main())
except:
  print()
  traceback.print_exc()
  print("\nThis is an unexpected error of fexit-%s\n" % version)
  print("To report this bug, send a screenshot ([Alt]+[PrintScreen])")
  print("to the author of fexit: framstag@rus.uni-stuttgart.de")
  wexit(127)
