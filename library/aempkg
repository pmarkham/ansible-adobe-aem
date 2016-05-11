#!/usr/bin/python

# Manage packages in Adobe CQ
#
# The installation of a bunch of hotfixes seems to have problems. CQ still seems to be process the upload and install even
# after it's returned from the http call. During this time it can also return odd http result codes (e.g. 404, 409, 503).
# To try and get around these issues, this program contains lots of retries. Pretty ugly, but it's the only way I could
# get it to work reliably.

import sys
import os
import platform
import httplib
import urllib
import base64
import json
import time
import xml.etree.ElementTree as ET

DOCUMENTATION = '''
---
module: aempkg
short_description: Manage Adobe CQ Packages
description:
    - Upload, install, uninstall and delete CQ packages
author: Paul Markham
notes:
    - At the moment, this module assumes that the files are available on the local machine to upload. An enhancement would be
      to get them from a binary repository or web server if they're needed.
    - The package installation is done in the background and while it's happening, CQ often returns errors if you issue
      any http calls to it. This makes it difficult to determine when a package is finished installing. This module catches
      errors and retries in an attempt to determine when the package is installed, however, occasionally it still fails.
      If this happens, re-running the module and it'll work.
options:
    name:
        description:
            - The name of the package
        required: true
    path:
        description:
            - Path to the file. Either a directory name, in which case it's assumed the file name matches the package name,
              or a file name if the  package name doesn't match the file name.
        required: false
    url:
        description:
            - url to the file. This will be passed to curl to download the package to /tmp. The package will be deleted from /tmp
              after it has been uploaded.
        required: false
    state:
        description:
            - State of the package
        required: true
        choices: [present, absent, uploaded, uninstalled]
    admin_user:
        description:
            - Adobe CQ admin user account name
        required: true
    admin_password:
        description:
            - Adobe CQ admin user account password
        required: true
    host:
        description:
            - Host name where Adobe CQ is running
        required: true
    port:
        description:
            - Port number that Adobe CQ is listening on
        required: true
    timeout:
        description:
            - Maximum time, in seconds, to wait for package to be installed.
        required: false
        default: 600
    force:
        description:
            - Force the packages to be uploaded and installed, even if it's already there. Note that using this is non-idempotent.
        required: false
        default: false
    wait:
        description:
            - sleep time, in seconds, after package installed before returning. Sometimes the install isn't quite complete, so give
              it a little extra time. Shouldn't really be necessary, but we haven't found a fool proof way of determining when the install is done.
        required: false
        default: 0
'''

EXAMPLES='''
# Upload and install package where the file name and package name are the same
- aempkg: name=cq-5.6.1-hotfix-3707-1.0.0.zip
         path=/var/packages
         state=present
         admin_user=admin
         admin_password=admin
         host=auth01
         port=4502

# Upload and install a package where the file name and package name are different
- aempkg: name=acs-aem-commons-content-1.6.2.zip
         path=/var/package/acs-aem-commons-content-1.6.2-min.zip
         state=present
         admin_user=admin
         admin_password=admin
         host=auth01
         port=4502
'''

# --------------------------------------------------------------------------------
# Helper function to walk the package list tree and extra info.
# --------------------------------------------------------------------------------

def find_pkg(data, pkg_name):
    tree = ET.fromstring(data)
    installed = False
    group = None
    result = None
    
    for pkg in tree.find('response/data/packages'):
        pkginfo = {}
        for i in pkg:
            pkginfo[i.tag] = i.text
        if pkginfo['downloadName'] == pkg_name:
            group = pkginfo['group']
            if pkginfo['lastUnpacked']:
                installed = True
            result = {'group': group, 'installed': installed}
            
    return result

# --------------------------------------------------------------------------------
# AEMPkg class.
# --------------------------------------------------------------------------------
class AEMPkg(object):
    def __init__(self, module):
        self.module         = module
        self.name           = self.module.params['name']
        self.state          = self.module.params['state']
        self.path           = self.module.params['path']
        self.url            = self.module.params['url']
        self.admin_user     = self.module.params['admin_user']
        self.admin_password = self.module.params['admin_password']
        self.host           = self.module.params['host']
        self.port           = self.module.params['port']
        self.timeout        = self.module.params['timeout']
        self.force          = self.module.params['force']
        self.wait           = float(self.module.params['wait'])
        
        self.curl_cmd       = self.module.get_bin_path('curl', True)
        self.changed        = False
        self.msg            = []

        self.get_pkg_info()

    # --------------------------------------------------------------------------------
    # Look up group info
    # --------------------------------------------------------------------------------
    def get_pkg_info(self, wait=True):
        start_time = time.time()
        while True:
            method = 'GET'
            url = '/crx/packmgr/service.jsp?cmd=ls'
            (status, output) = self.http_request(method, url)
            if status < 200 or status > 299:
                if wait:
                    now = time.time()
                    if now - start_time > self.timeout:
                        self.module.fail_json(msg="get_pkg_info: timed out trying to get package info")
                    time.sleep(30)
                    continue
                else:
                    self.module.fail_json(msg="get_pkg_info: http request '%s %s' failed: %s %s" % (method, url, status, output))
            pkg_info = find_pkg(output, self.name)
            if pkg_info == None:
                self.pkg_uploaded = False
                self.pkg_installed = False
                self.group = None
            else:
                self.pkg_uploaded = True
                self.pkg_installed = pkg_info['installed']
                self.group = pkg_info['group']
            break

    # --------------------------------------------------------------------------------
    # state='present'
    # --------------------------------------------------------------------------------
    def present(self):
        if not self.pkg_uploaded or self.force == 'yes':
            self.upload_pkg()
        if not self.pkg_installed or self.force == 'yes':
            self.install_pkg()

    # --------------------------------------------------------------------------------
    # state='absent'
    # --------------------------------------------------------------------------------
    def absent(self):
        if self.pkg_installed or self.force == 'yes':
            self.uninstall_pkg()
        if self.pkg_uploaded or self.force == 'yes':
            self.delete_pkg()

    # --------------------------------------------------------------------------------
    # state='uploaded'
    # --------------------------------------------------------------------------------
    def uploaded(self):
        if not self.pkg_uploaded:
            self.upload_pkg()

    # --------------------------------------------------------------------------------
    # state='uninstalled'
    # --------------------------------------------------------------------------------
    def uninstalled(self):
        if self.pkg_installed:
            self.uninstall_pkg()

    # --------------------------------------------------------------------------------
    # Upload a package.
    #
    # NOTE: this is ugly and uses curl to upload the package until I can figure
    #       out the Python code to do it.
    #
    # WARNING: This leaves the admin_username and admin_password exposed to a ps command.
    #
    # TODO: re-implement this (perhaps using code from
    #       http://code.activestate.com/recipes/578846-composing-a-postable-http-request-with-multipartfo/)
    # --------------------------------------------------------------------------------
    def upload_pkg(self):
        if not self.path and not self.url:
            self.module.fail_json(msg='Missing required argument: path or url')

        start_time = time.time()
        while True:
            if self.url:
                file = '/tmp/' + os.path.basename(self.url)
                if not self.module.check_mode:
                    cmd="%s -s -w '%%{http_code}' -o %s %s" % (self.curl_cmd, file, self.url)
                    (rc, out, err) = self.module.run_command(cmd)
                    if rc != 0 or out != '200':
                        if os.path.isfile(file):
                            os.remove(file)
                        self.module.fail_json(msg='upload_pkg: failed to retrieve package: rc=%s stdout=%s stderr=%s' % (rc, out, err))
                    self.msg.append('package retrieved')
            else:
                file = self.path
                if not os.path.isfile(file):
                    file = '%s/%s' % (self.path, self.name)
                if not os.path.isfile(file):
                    self.module.fail_json(msg="upload_pkg: File '%s' doesn't exist" % file)
            if not self.module.check_mode:
                cmd="%s -u %s:%s -v -q -F package='@%s' http://%s:%d/crx/packmgr/service/.json/?cmd=upload" % (self.curl_cmd, self.admin_user, self.admin_password, file, self.host, self.port)
                (rc, out, err) = self.module.run_command(cmd)
                now = time.time()
                if rc != 0:
                    if now - start_time > self.timeout:
                        self.module.fail_json(msg='upload_pkg: Package upload failed: rc=%s stdout=%s stderr=%s' % (rc, out, err))
                    else:
                         time.sleep(30)
                         continue

                self.get_pkg_info(wait=True)
                if not self.pkg_uploaded:
                    if now - start_time > self.timeout:
                        self.module.fail_json(msg="upload_pkg: Error: can't find package '%s' after upload. %s - %s" % (self.name, out, err))
                    else:
                        time.sleep(30)
                        continue
            if self.url and os.path.isfile(file):
                os.remove(file)
            break

        self.changed = True
        self.msg.append('package uploaded')

    # --------------------------------------------------------------------------------
    # Install a package. Must already have been uploaded.
    # --------------------------------------------------------------------------------
    def install_pkg(self):
        if not self.module.check_mode:
            start_time = time.time()
            while True:
                url = '/crx/packmgr/service/.json/etc/packages/%s/%s?cmd=install' % (self.group, urllib.quote(self.name))
                (status, output) = self.http_request('POST', url)
                if status < 200 or status > 299:
                    now = time.time()
                    if now - start_time > self.timeout:
                        self.module.fail_json(msg="install_pkg: http request '%s %s' failed: %s %s" % ('POST', url, status, output))
                    else:
                        time.sleep(30)
                        continue
                try:
                    data = json.loads(output)
                except Exception as e:
                    now = time.time()
                    if now - start_time > self.timeout:
                        self.module.fail_json(msg='install_pkg: failed to decode JSON: %s %s' % (e, output))
                    else:
                        time.sleep(30)
                        continue
                if not data['success']:
                    now = time.time()
                    if now - start_time > self.timeout:
                        self.module.fail_json(msg='install_pkg: Package install failed: %s - %s' % (url, data['msg']))
                    else:
                        time.sleep(30)
                        continue
                self.wait_for_completion()
                break
        time.sleep(self.wait)
        self.changed = True
        self.msg.append('package installed')

    # --------------------------------------------------------------------------------
    # Uninstall a package.
    # --------------------------------------------------------------------------------
    def uninstall_pkg(self):
        if not self.module.check_mode:
            method = 'POST'
            url = '/crx/packmgr/service/.json/etc/packages/%s/%s?cmd=uninstall' % (self.group, urllib.quote(self.name))
            (status, output) = self.http_request(method, url)
            if status < 200 or status > 299:
                self.module.fail_json(msg="http request '%s %s' failed: %s %s" % (method, url, status, output))
            data = json.loads(output)
            if not data['success']:
                self.module.fail_json(msg='Package uninstall failed: %s - %s' % (url, data['msg']))
            self.wait_for_completion()
        self.changed = True
        self.msg.append('package uninstalled')

    # --------------------------------------------------------------------------------
    # Delete a package.
    # --------------------------------------------------------------------------------
    def delete_pkg(self):
        if not self.module.check_mode:
            method = 'POST'
            url = '/crx/packmgr/service/.json/etc/packages/%s/%s?cmd=delete' % (self.group, urllib.quote(self.name))
            (status, output) = self.http_request(method, url)
            if status < 200 or status > 299:
                self.module.fail_json(msg="http request '%s %s' failed: %s %s" % (method, url, status, output))
            data = json.loads(output)
            if not data['success']:
                self.module.fail_json(msg='Package delete failed: %s - %s' % (url, data['msg']))
        self.changed = True
        self.msg.append('package deleted')

    # --------------------------------------------------------------------------------
    # Installing a package can make the system return HTTP errors while it's
    # being installed in the background.
    # Poll the server and wait for it to start returning pages before continuing.
    # --------------------------------------------------------------------------------
    def wait_for_completion(self):
        start_time = time.time()
        while True:
            url = '/crx/packmgr/service.jsp?cmd=ls'
            (status, output) = self.http_request('GET', url)
            if status == 200:
                break
            if (time.time() - start_time) > self.timeout:
                self.module.fail_json(msg='Timed out waiting for package install')
            time.sleep(30)

    # --------------------------------------------------------------------------------
    # Issue http request.
    # --------------------------------------------------------------------------------
    def http_request(self, method, url):
        headers = {'Authorization' : 'Basic ' + base64.b64encode(self.admin_user + ':' + self.admin_password)}
        if method == 'POST':
            if self.force == 'yes':
                fields = [('recursive', 'true'), ('force', 'true')]
            else:
                fields = [('recursive', 'true')]
            data = urllib.urlencode(fields)
            headers['Content-type'] = 'application/x-www-form-urlencoded'
        else:
            data = None
        conn = httplib.HTTPConnection(self.host + ':' + str(self.port))
        try:
            conn.request(method, url, data, headers)
        except:
            return(9999, '')

        resp = conn.getresponse()
        return (resp.status, resp.read())

    # --------------------------------------------------------------------------------
    # Return status and msg to Ansible.
    # --------------------------------------------------------------------------------
    def exit_status(self):
        if self.changed:
            msg = ','.join(self.msg)
            self.module.exit_json(changed=True, msg=msg)
        else:
            self.module.exit_json(changed=False)


# --------------------------------------------------------------------------------
# Mainline.
# --------------------------------------------------------------------------------
def main():
    module = AnsibleModule(
        argument_spec      = dict(
            name           = dict(required=True),
            state          = dict(required=True, choices=['present', 'absent', 'uploaded', 'uninstalled']),
            path           = dict(default=None),
            url            = dict(default=None),
            admin_user     = dict(required=True),
            admin_password = dict(required=True, no_log=True),
            host           = dict(required=True),
            port           = dict(required=True, type='int'),
            timeout        = dict(default=600, type='int'),
            force          = dict(default='no', choices=['yes', 'no']),
            wait           = dict(default=0, type='int'),
            ),
        supports_check_mode=True
        )

    pkg = AEMPkg(module)

    state = module.params['state']

    if state == 'present':
        pkg.present()
    elif state == 'uploaded':
        pkg.uploaded()
    elif state == 'uninstalled':
        pkg.uninstalled()
    elif state == 'absent':
        pkg.absent()
    else:
        module.fail_json(msg='Invalid state: %s' % state)

    pkg.exit_status()

# --------------------------------------------------------------------------------
# Ansible boiler plate code.
# --------------------------------------------------------------------------------
from ansible.module_utils.basic import *
main()
