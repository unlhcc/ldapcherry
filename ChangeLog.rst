Dev
***

* [sec ] fix XSS injection in the url redirect in the login page (thanks to jthiltges)
* [impr] more systematic use of html and url escaping in the html rendering to prevent against content injection (thanks to jthiltges)

Version 0.5.2
*************

* [fix ] regression in 0.5.1, setup.py could not work without the dependencies already installed

Version 0.5.1
*************

* [impr] cleaner align of labels (input-group-addon width)

Version 0.5.0
*************

* [feat] add handling of textfielf (thanks to Stan Rudenko)
* [fix ] fix ldap.group_attr.<attr> handling with attr different than dn (uid for example)
* [impr] removing duplicate option in form select fields
* [impr] add dynamic resizing to align form labels (input-group-addon width)

Version 0.4.0
*************

* [impr] add unit test for multi backend setup
* [fix ] notify on add in case if user is already in one backend
* [fix ] notify on modify in case if user is not in every backend
* [fix ] delete user in all backends even if it doesn't exist in one of them
* [fix ] fix bad handling of = or & in passwords in ppolicy checker (js)
* [fix ] fix many encoding errors in AD backend
* [impr] add unit tests on AD backend
* [impr] display the admin result page if searching as admin in navbar form

Version 0.3.5
*************

* [fix ] fix error in ad backend when self modifying password

Version 0.3.4
*************

* [impr] focus on first field for all forms 
* [impr] add icon in navbar to return on /

Version 0.3.3
*************

* [fix ] add html escape for fields display
* [impr] disable minimum search lenght for admin search

Version 0.3.2
*************

* [fix ] fix many encoding errors on login and password

Version 0.3.1
*************

* [fix ] better and "html" correct display of user's attributes

Version 0.3.0
*************

* [impr] add focus on first input of forms
* [impr] add 404 (default) handler and its error page
* [feat] add a -D switch to ldapcherryd which enables logging to stderr in foreground
* [feat] print user's attribute on index page

Version 0.2.5
*************

* [fix ] encoding issues for passwords and cn in ad backend
* [fix ] fix minimum lenght of 3 in search (no empty search, and server side check)
* [impr] disable form autofilling (annoying in firefox), kind of a hack...

Version 0.2.4
*************

* [fix ] use post instead of get for ppolicy validation
* [fix ] impose a minimum lenght of 3 for searches
* [fix ] fix the maxuid in uid calculation in js

Version 0.2.3
*************

* [fix ] notifications missing in case of multiple notification waiting to be displayed
* [fix ] password handling for Active Directory backend 
* [fix ] default attribute value handling
* [fix ] corrections on exemple configuration
* [impr] explicite mandatory attributes for Active Directory backend

Version 0.2.2
*************

* [fix ] fix pypi release
* [impr] better error/log messages

Version 0.2.1
*************

* [fix ] fix doc 

Version 0.2.0
*************


* [feat] custom error messages for ppolicy error in forms
* [feat] add visual notifications after actions
* [impr] code reorganization
* [impr] better unit tests on the demo backend
* [impr] better unit tests on authentication

Version 0.1.0
*************

* [feat] add demo backend
* [feat] add custom javascript hook
* [feat] add documentation for backends
* [feat] add the Active Directory backend
* [feat] add display name parameter for backends
* [fix ] fix many encoding error in LDAP backend
* [fix ] fix dn renaming of an entry in LDAP backend
* [impr] turn-off configuration monitoring
* [impr] better exception handling and debugging logs

Version 0.0.1
*************

* [misc] first release
