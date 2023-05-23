%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LATEX TEMPLATE FOR MASTER THESIS AT CHALMERS UNIVERSITY OF TECHNOLOGY %
% CREATED BY DAVID FRISK, 2014						%
%									%
% BASED ON GUIDELINES FOUND ON 						%
% https://student.portal.chalmers.se/en/chalmersstudies/		%
% masters-thesis/Pages/design-and-publish-masters-thesis.aspx           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

INFO:

This template has been constructed based on the following documents and webpages:

* Design and publish masters thesis (https://student.portal.chalmers.se/en/chalmersstudies/masters-thesis/Pages/design-and-publish-masters-thesis.aspx)

* Language policy of chalmers (available on http://www.chalmers.se/insidan/EN/tools/language-issues)

* Regulations for language issues at chalmers (available on http://www.chalmers.se/insidan/EN/tools/language-issues)

* Layout of the thesis (http://www.chalmers.se/insidan/EN/tools/design-manual/templates/layout-thesis)


GENERAL NOTES:

* To create a perspicuous structure of the report source code, each chapter (Abstract, Acknowledgements, Introduction, Methods etc.) is put in a separate .tex file placed in the "include" folder. 

* The packages and settings defining the output of the source code have, for the reason mentioned above, also been put in a separate .tex file called PackagesSettings.tex . This file starts with some basic settings and ends with some optional settings used to tune the layout of the report, hence the latter ones can be modified or removed if desired.

* Separate .tex files in the "include" folder are imported into the main file Report_template.tex using the command "input", e.g. "\input{include/Methods}". 

