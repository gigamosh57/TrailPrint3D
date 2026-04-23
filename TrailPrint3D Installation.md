INTRODUCTION
This is a Addon for Blender that allows you to create Miniature Maps of your adventures from just the GPX file that you can download from Komoot, strava, garmin or other tracking apps!

 

SUPPORT MY WORK
PATREON
Buy me a Coffee
 
Get Help and share your Creations on my Discord server:
Join Discord

 

HOW TO INSTALL
Please Watch the Video on Top first as it contains a full Installation Guide and Addon Tutorial
Download the latest Blender version from https://www.blender.org/download/
Download the Addon from this Page ("TrailPrint3D-x_x.py" file from “Download STL/CAD Files” | use browser version)


Open Blender, and go to Edit → Preferences

Go to the Addons tab, Click the top right Arrow and then “Install From Disk”

Select the TrailPrint3D_x-x.py file you downloaded and confirm
Close the popup window

If the sidebar is not showing, Press “N”
If “TrailPrint3D” is displayed there, the installation was a success
The addon was tested with Blender 4.5.2 and i would reccomend using the newest version available

it does NOT work for Blender 4.4 and below

 

PARAMETERS

Generate: Generates the Map with your Current set parameters
File Path: The .GPX file you want to import. Click the little folder to open a File Explorer
Export Path: The Folder the STL files will be saved
Trail Name: The name of the save file. Keep it blank to use the name of the file
Shape: The shape of the Map
Resolution: The “Quality” of the map. Higher = Better quality but also longer Generating times. i reccomend a maximum of 6 or 7 ( 7 takes up to 10 minutes).
Elevation scale: Multiplier to the elevation. Use it to make flat maps more interesting or to flatten down steep landscapes
Path thickness: the thickness of the path
Path scale: The size of the path compared to the map. If your object size is 100 and Path scale is 0.5, then the path is about 50mm big. if pathScale is 0.75 its about 75mm big.
Overwrite path elevation: If your .GPX has a offset to the real world elevation (happened sometimes for me on komoot) you can check this box and it rewrites the elevation so it matches the map terrain
Advanced Parameters (In the Advanced Tab)
Export STL/Obj: Export the Currently selected Object as STL or OBJ if it has materials applied to it
Map : Parameters about the Map
Fixed elevation Scale: The diffrence between the highest and lowest point on the map will be 10mm
minThickness: Thickness of the thinnest point of the map in mm
ShapeRotation: Rotates the shape. Useful for shapes like the hearth where you need to rotate the shape so the path fits perfectly on the map
xTerrainOffset: Offset of the map in X Direction to the center of the path
yTerrainOffset: Offset of the map in Y Direction to the center of the path
SingleColorMode: Generates the Map and the Trail so they can be printed separately and assembled afterwards
Tolerance: The tolerance between the Map and the Trail for the SingleColorMode
DisableCache: Disables the Cache for Opentopodata and Open-elevation
CacheSize: The CacheSize for Opentopodata and Open-elevation
Custom Maps (Patreon Version): Allows you to Extend your Map or to Generate Maps based on Coordinates
Multi Generation (Patreon Version): Allows you to Generate a Map from multiple .GPX files
Include Elements:
Include Water/Forests/City Boundaries: Automatic Coloring of Water, Forests and Cities
Size Treshold: Only generates them if the elements are bigger than X Blender Units
Paint Map: Choose if you want those Elements to be directly painted onto the map or generate them as separate objects
Pin:
Latitude/Longitude: Input a Point
Pin on Coords: Generate a Pin on that Point
Cityname (Patreon Version): Enter a Cityname
Pin on City (Patreon Version): Place a Pin on the Cityname
Special (Patreon Version):
Allows you to Import a special .Blend File from my Patreon to Create Slider or Jigzaw Puzzles of your Maps
Post-Process:
Mountain Treshole: The Treshold at what height mountains should start
Color Mountains: Paint the Currently selected Map from the given Treshold
Contour Line Thickness: Thickness of the Contour lines (reccomend layer thickness or a multiple of it)
Contour Line distance: Distance from the start of one contour line to the next one
Contour Line offset: The offset at what height the Contour lines should start
Contour Lines: Generate the Contour Lines as a separate Object
Rescale: Set a scale and click “Rescale Elevation” with a Map selected to Change the Elevation without having to regenerate it
Extrude: Extrude the Terrain of the currently selected map by the set Value
Magnet holes: Set a Magnet diameter and height, press “Add Magnet Holes” to add Magnet holes on the bottom of the currently selected Map
Add dovetail Cutouts: Add Dovetail Cutouts to the Currently selected Map
Add Bottom Mark: Add the Object Name to the Bottom of the Map (For better identification)
Bottom mark cutout: Enable this so the Bottom mark cutout will be a negative instead of a separate object
Preset:
Save and load Presets
Load Preset: Load the currently selected preset
Save Preset: Save your current Settings under a Name you can Enter
Delete Preset: Delete the currently selected preset
API:
Select from one of 3 Diffrent APIs. Terrain-Tiles is selected by default. Only switch if you have problems with one of them
Additional Info:
Generation Settings: Select a Map and click this Button to get infos about the Generation settings of that Map
Mainly for debugging, finding Errors or to check what settings were used to create a map
Attribution:
Credit to the Datasources that made the Addon possible
 

Shape Parameters:

When a shape with Text is selected a new Panel “Additional shape settings” appears at the bottom of the sidebar
Font: Set the font of the Text
Text Size: Set the size of the Text
Text Size Title: Optional Text size for the Title.
Overwrite Text: Replace the Text of the 3 bottom Text blocks
Plate Thickness: Thickness of the Baseplate
BorderSize: Size of the base compared to the Size → 20% means Base is 20% Bigger than the map
PlateInsertvalue: Insert into the Plate for better alignment of the Map if Plate and Map are printed separately
TextAngle: angle of the Text rotated around the center
FILAMENT IM USING
I usually use 5 Colors (Reflinks)

Green as basecolor (Amazon)
Red for the path (Amazon)
Blue for water (Amazon)
Grey for mountains (Amazon)
Dark Green for Forests (Amazon)
 

 

PATREON VERSION
 


I Spend hundreds of Hours on this Addon, Improving, Testing, and you can downlaod it here for Free. But Without my Patreon Supporters that wouldnt have been possible. Thats why the Patreon Version has some Extra Features and you can also get them by Supporting my Work. Here are some of the Extra Features

Additional Shapes
Special Shapes inkl Tutorial (Sliding Puzzle or Jigzaw Puzzle)
Place Pins by Entering a City name
Chain Together multiple .GPX files together to a single one
Create Maps that contain multiple .GPX files
Create custom Shapes
Extend Maps endlessly

UPDATELOG
29.03.2025 Version 1.2

30.03.2025 Version 1.3

01.04.2025 Version 1.5

12.04.2025 Version 1.6

21.04.2025 Version 1.7

25.04.2025 Version 1.8

08.05.2025 Version 1.9

13.09.2025 Version 2.2

03.12.2025 Version 2.5

23.04.2026 Version 2.52
Updated by @gigamosh57 (original addon by EmGi)
- OSM updates: improved OpenStreetMap feature and boundary handling for cleaner generated overlays
- Logging updates: improved detailed logging and log-file writing support for easier troubleshooting
- Scaling updates: refined map/path scaling behavior for more consistent sizing and elevation workflows
- Lake updates: improved water/lake area handling for better map water representation
