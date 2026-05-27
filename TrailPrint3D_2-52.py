# Copyright (c) 2025 EmGi
#
# This work is licensed under the Creative Commons Attribution-NonCommercial 4.0 
# International License. To view a copy of this license, visit 
# https://creativecommons.org/licenses/by-nc/4.0/
#

#  Attribution
# Elevation data provided by the Mapzen Terrain Tiles project.
# © Mapzen. Data hosted on AWS as part of the AWS Public Dataset Program.
# License: https://github.com/tilezen/joerd/blob/master/docs/attribution.md
# Elevation data from OpenTopoData, using the SRTM and other datasets.
# Elevation data from Open-Elevation, based on Shuttle Radar Topography Mission (SRTM) data © NASA.
# Water data © OpenStreetMap contributors
# Terrain data from Mapzen, based on data © OpenStreetMap contributors, NASA SRTM, and USGS.

#Map data © OpenStreetMap contributors

'''
Version 2.5
- Added Icons to Buttons
- Added Preset Feature
- Bugfixes:
    xTerrain/yTerrain Offset not working correctly with Text based Shapes
    Shape Rotation not working correctly with Text based Shapes
    Magnetholes/Dovetails not working correctly with Text based Shapes
    Magnetholes/Dovetails not working correctly with Rotated Shapes



'''

bl_info = {
    "name": "TrailPrint3D",
    "blender": (4, 5, 2),
    "category": "Object",
    "author": "EmGi",
    "version": (2,52),
    "description": "Create 3D Printable Miniature Maps of your Adventures",
    "warning": "",
    "doc_url": "",
    "tracker_url": "",
    "support": "COMMUNITY"
}

category = "TrailPrint3D"
AddonVersion = (2, 52)


import bpy # type: ignore
import webbrowser
import xml.etree.ElementTree as ET
import math
import requests # type: ignore
import time
from datetime import date
from datetime import datetime
import bmesh # type: ignore
from mathutils import Vector, bvhtree, Euler
import os
import sys
import json
import platform
import zlib
import struct
import csv
import functools
import logging
import random
import hashlib
from urllib.parse import urlencode
from urllib.request import Request, urlopen
from logging.handlers import RotatingFileHandler

try:
    import rasterio # type: ignore
except ImportError:
    rasterio = None


gpx_file_path = ""
exportPath = ""
shape = ""
name = ""
size =  48
num_subdivisions = 4
scaleElevation = 5
pathThickness = 1.2
pathScale = 0.8
shapeRotation = 0
overwritePathElevation = False
autoScale = 1
dataset = "srtm30m"  # OpenTopoData dataset

textFont = ""
textSize = 0
overwriteLength = ""
overwriteHeight = ""
overwriteTime = ""
outerBorderSize = 0

minLat = 0
maxLat = 0
minLon = 0
maxLon = 0

lowestZ = 0
highestZ = 0


overwritePathElevation = False
centerx = 0
centery = 0
total_length = 0
total_elevation = 0
total_time = 0
time_str = ""
elevationOffset = 0
# Conversion factor: 1 degree latitude/longitude ≈ 111320 meters
LAT_LON_TO_METERS = 111.32
additionalExtrusion = 0
specialCollection = [("----", "----", "")]
duration = 0
api = 0
fixedElevationScale = False
minThickness = 2
selfHosted = ""
opentopoAdress = ""
GPXsections = 0

scaleHor = 0

MapObject  = None
plateobj = None
textobj = None
objWater = None
objForest = None
objCity = None
objGlacier = None

# Define a path to store the counter data
counter_file = os.path.join(bpy.utils.user_resource('CONFIG'), "api_request_counter.json")
elevation_cache_file = os.path.join(bpy.utils.user_resource('CONFIG'), "elevation_cache.json")
# Set up a cache directory for Terrarium tiles
terrarium_cache_dir = os.path.join(bpy.utils.user_resource('CONFIG'), "terrarium_cache")
if not os.path.exists(terrarium_cache_dir):
    os.makedirs(terrarium_cache_dir)
tnm_3dep_cache_dir = os.path.join(bpy.utils.user_resource('CONFIG'), "tnm_3dep")
if not os.path.exists(tnm_3dep_cache_dir):
    os.makedirs(tnm_3dep_cache_dir)

# In-memory elevation cache
_elevation_cache = {}
cacheSize = 100000

buggyDataset = 0
exportformat = "STL"
module_logger = logging.getLogger("TrailPrint3D")
module_logger.addHandler(logging.NullHandler())
module_logger.propagate = False


def _resolve_log_folder(props):
    export_dir = bpy.path.abspath(props.export_path) if props and props.export_path else ""
    if export_dir and os.path.isdir(export_dir):
        return export_dir
    temp_dir = bpy.app.tempdir or bpy.utils.user_resource('TEMP')
    return bpy.path.abspath(temp_dir) if temp_dir else bpy.utils.user_resource('CONFIG')


def init_module_logger(context=None):
    props = getattr(context.scene, "tp3d", None) if context and getattr(context, "scene", None) else None
    if props is None:
        return module_logger
    log_folder = _resolve_log_folder(props)
    log_filename = (props.debug_log_filename or "trailprint3d.log").strip() or "trailprint3d.log"
    log_path = os.path.join(log_folder, log_filename)
    desired_level = getattr(logging, props.debug_log_level, logging.INFO)
    enabled = props.debug_logging_enabled

    for handler in list(module_logger.handlers):
        if isinstance(handler, RotatingFileHandler):
            module_logger.removeHandler(handler)
            handler.close()

    module_logger.setLevel(desired_level if enabled else logging.CRITICAL + 1)
    if enabled:
        file_handler = RotatingFileHandler(log_path, maxBytes=2 * 1024 * 1024, backupCount=3, encoding="utf-8")
        file_handler.setLevel(desired_level)
        file_handler.setFormatter(logging.Formatter("%(asctime)s | %(levelname)s | %(funcName)s | %(message)s"))
        module_logger.addHandler(file_handler)
        module_logger.info("Logger initialized at %s", log_path)
    return module_logger


def logging_settings_update(self, context):
    init_module_logger(context)


def log_workflow(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        if module_logger.isEnabledFor(logging.DEBUG):
            module_logger.debug("ENTER %s", func.__name__)
        try:
            result = func(*args, **kwargs)
            if module_logger.isEnabledFor(logging.DEBUG):
                module_logger.debug("EXIT %s", func.__name__)
            return result
        except Exception:
            module_logger.exception("EXCEPTION in %s", func.__name__)
            raise
    return wrapper

#PANEL----------------------------------------------------------------------------------------------------------

def shape_callback(self,context):
    #print(f"Shape: {self.shape}")
    if self.shape == "HEXAGON INNER TEXT" or self.shape == "HEXAGON OUTER TEXT" or self.shape =="OCTAGON OUTER TEXT" or self.shape == "HEXAGON FRONT TEXT":
        try:
            bpy.utils.register_class(MY_PT_Shapes)
        except:
            pass
    else:
        try:
            bpy.utils.unregister_class(MY_PT_Shapes)
        except:
            pass

# Cache the collection names
def get_external_collections(path):
    if not os.path.exists(path):
        return []
    with bpy.data.libraries.load(path, link=True) as (data_from, _):
        return list(data_from.collections)

# Update dropdown items dynamically when panel is drawn
def update_collection_items(self, context):

    print("Updating")
    path = bpy.context.scene.tp3d.specialBlend_path
    path = bpy.path.abspath(path)
    names = get_external_collections(path)
    print(names)
    global specialCollection
    specialCollection = [(name, name, "") for name in names]
    #return [(name, name, "") for name in names]

def dynamic_specialCollection_items(self, context):
    return specialCollection
    
# Define a Property Group to store variables
class MyProperties(bpy.types.PropertyGroup):
    file_path: bpy.props.StringProperty(
        name="File Path",
        description="Select a file",
        default="",
        maxlen=1024,
        subtype='FILE_PATH'  # Enables file selection
    )# type: ignore
    export_path: bpy.props.StringProperty(
        name="Export Path",
        description="Where to save the STL file",
        default="",
        maxlen=1024,
        subtype='DIR_PATH'  # Enables folder selection
    )# type: ignore
    chain_path: bpy.props.StringProperty(
        name="Folder Path",
        description="Select a folder that contains multiple GPX files",
        default="",
        maxlen=1024,
        subtype='DIR_PATH'  # Enables folder selection
    )# type: ignore
    trailName: bpy.props.StringProperty(name="Name", default="", description="Leave empty to use the Filename") # type: ignore
    
    shape: bpy.props.EnumProperty(
        name = "Shape",
        items=[
            ("HEXAGON", "Hexagon", "Hexagonal map"),
            ("SQUARE", "Square", "Square map"),
            #("CIRCLE", "Circle", "Circular map"),
            #("OCTAGON", "Octagon", "Octagon Map"), #Premium
            #("ELLIPSE", "Ellipse", "Ellipse Map"), #Premium
            #("HEART", "Heart", "Heart Map"), #Premium
            ("HEXAGON INNER TEXT", "Hexagon inner text", "Hexagonal map with inserted Text"),
            ("HEXAGON OUTER TEXT", "Hexagon outer text", "Hexagonal map with backplate and text"),
            ("HEXAGON FRONT TEXT", "Hexagon front text", "Hexagonal map with backplate and text on the front")
            #("OCTAGON OUTER TEXT", "Octagon outer text", "Octagon map with backplate and text") #Premium
        ],
        default = "HEXAGON",
        update = shape_callback #calls shape_callback when user selects diffrent shape to register the Shape Panel
    )# type: ignore
    
    api: bpy.props.EnumProperty(
        name = "api",
        items=[
            ("OPENTOPODATA", "Opentopodata", "Slower but more accurate elevation"),
            ("OPEN-ELEVATION","Open-Elevation","Faster but some regions are low quali"),
            ("USGS_TNM", "USGS TNM", "Uses The National Map elevation point query endpoint"),
            ("TERRAIN-TILES", "Terrain-Tiles", "Currently Fastest available set")
        ],
        default = "TERRAIN-TILES"
    )# type: ignore

    dataset: bpy.props.EnumProperty(
        name = "Dataset",
        items=[
            ("srtm30m", "srtm30m", "Latitudes -60 to 60"),
            ("aster30m","aster30m","global"),
            ("ned10m","ned10m","Continental USA, Hawaii, parts of Alaska"),
            ("mapzen","mapzen","global"),
            ("nzdem8m","nzdem8m","New Zealand 8m"),
            ("eudem25m","eudem25m","Europe")
        ],
        default = "aster30m"
    )# type: ignore

    scalemode: bpy.props.EnumProperty(
        name="scalemode",
        items=[
            ('FACTOR', "Map Scale", "Set a scale based on the Map size"),
            ('COORDINATES', "Coordinates", "Calculate the scale by using 2 Coordinates (Lat/lon)"),
            ('SCALE', "Global Scale", "Set a scale based on the Global Scale (Mercator Projection)")
        ],
        default='FACTOR'
    )# type: ignore
    pathScale: bpy.props.FloatProperty(name = "Path Scale", default = 0.8, min = 0.01, max = 200, description = "Scale of Path in Relation to the Mapsize/GlobalScale (depending on scalemode)")
    scaleLon1: bpy.props.FloatProperty(name = "Lon1", default = 0, description = "The Longitude of the first coordinate")
    scaleLat1: bpy.props.FloatProperty(name = "Lat1", default = 0, description = "The Latitude of the first coordinate")
    scaleLon2: bpy.props.FloatProperty(name = "Lon2", default = 0, description = "The Longitude of the second coordinate")
    scaleLat2: bpy.props.FloatProperty(name = "Lat2", default = 0, description = "The Latitude of the second coordinate")

    selfHosted: bpy.props.StringProperty(name="Self Hosted API", default="", description="Has to be same API format as Opentopodata.org (https://api.opentopodata.org/v1/)")

    objSize: bpy.props.IntProperty(name="Object Size in mm", default = 100, min = 5, max = 10000,description = "Size of the map in mm")
    num_subdivisions: bpy.props.IntProperty(name = "Resolution", default = 4, min = 1, max = 10, description = "(max reccomended 8) Higher Number = more detailed terrain but slower generation")
    scaleElevation: bpy.props.FloatProperty(name = "Elevation Scale", default = 10, min = 0, max = 10000, description = "Multiplier to the Elevation")
    pathThickness: bpy.props.FloatProperty(name = "Path Thickness", default = 1.2, min = 0.1, max = 5, description = "Thickness of the path in mm")
    pathRemeshEnabled: bpy.props.BoolProperty(name="Path Remesh", default=True, description="Apply voxel remesh to trails before booleans")
    shapeRotation: bpy.props.IntProperty(name = "ShapeRotation", default = 0, min = -360, max = 360, description = "Rotation of the shape") 
    overwritePathElevation: bpy.props.BoolProperty(name="Overwrite Path Elevation", default=True, description = "Cast each point of the trail onto the Terrain Mesh")
    o_verticesPath: bpy.props.StringProperty(name="Path vertices ", default="")
    o_verticesMap: bpy.props.StringProperty(name="Path Map ", default="")
    o_mapScale: bpy.props.StringProperty(name="Map Scale", default = "")
    o_time: bpy.props.StringProperty(name="TimeTook",default="")
    o_apiCounter_OpenTopoData: bpy.props.StringProperty(name="apiCounter_OpenTopodata", default = "API Limit: ---/1000 daily")
    o_apiCounter_OpenElevation: bpy.props.StringProperty(name="apiCounter_OpenElevation", default = "API Limit: ---/1000 monthly")
    o_elevationApiStatus: bpy.props.StringProperty(name="elevationApiStatus", default = "Status: not tested")
    o_centerx: bpy.props.FloatProperty(name = "Center X", default = 0, description = "X Center of the Path")
    o_centery: bpy.props.FloatProperty(name = "Center Y", default = 0, description = "y Center of the Path")

    magnetHeight: bpy.props.FloatProperty(name = "Magnet Height", default = 2.5, description = "Height of the Holes for Magnets")
    magnetDiameter: bpy.props.FloatProperty(name = "Magnet Diameter", default = 6.3, description = "Diameter of the Holes for Magnets")

    bottomMarkCutout: bpy.props.BoolProperty(name="Bottom Mark Cutout", default = False, description = "Creates Bottom mark as a Cutout")

    textFont: bpy.props.StringProperty(
        name="Font",
        description="Select a file",
        default="",
        maxlen=1024,
        subtype='FILE_PATH'  # Enables file selection
    )# type: ignore
    textSize: bpy.props.IntProperty(name="Text Size", default = 5, min = 0, max = 1000)
    textSizeTitle: bpy.props.IntProperty(name="Title Text Size", default = 0, min = 0, max = 1000, description = "Keep 0 to use value from 'Text Size'")
    overwriteLength: bpy.props.StringProperty(name="text1", default = "")
    overwriteHeight: bpy.props.StringProperty(name="text2", default = "")
    overwriteTime: bpy.props.StringProperty(name="text3", default = "")
    outerBorderSize: bpy.props.IntProperty(name="BorderSize in %", default = 20, min = 0, max = 1000, description="Only for Shapes with Plate")
    text_angle_preset: bpy.props.IntProperty(name="Text Angle", description="Rotate Text on Shape", default=0, min = 0, max = 260)
    plateThickness: bpy.props.FloatProperty(name="plateThickness", default = 5, description="Thickness of the Additional Plate")
    plateInsertValue: bpy.props.FloatProperty(name="plateInsertValue", default = 0, description="Depth of Cutout for the Map in the Plate, 0  to ignore")

    tileSpacing: bpy.props.FloatProperty(name="tileSpacing", default = 0, description="Distance between Tiles when Extending")



    minThickness: bpy.props.IntProperty(name="minThickness", default = 2, min = 0, max = 1000, description="Additional Thickness on lowest point")
    xTerrainOffset: bpy.props.FloatProperty(name="xTerrainOffset", default = 0, description="Gives the map an Offset in X-Direction from the path")
    yTerrainOffset: bpy.props.FloatProperty(name="yTerrainOffset", default = 0, description="Gives the map an Offset in Y-Direction from the path")

    rescaleMultiplier: bpy.props.FloatProperty(name = "scale", default = 1, min = 0, max = 10000)
    thickenValue: bpy.props.FloatProperty(name="thickenValue", default = 1, description = "Makes your Map 1mm thicker")
    fixedElevationScale: bpy.props.BoolProperty(name="FixedElevationScale(10mm)", default=False, description = "Force the elevation to be 10mm High from highest to lowest point (ElevationScale still applies after that)")
    singleColorMode: bpy.props.BoolProperty(name="SingleColorMode", default = False, description = "Enable this if you dont have a Multicolor printer")
    tolerance: bpy.props.FloatProperty(name="Tolerance", default = 0.2, description="Tolerance of the Trail for the SingleColorMode")
    disableCache: bpy.props.BoolProperty(name="disableCache", default = False, description = "disabling cache if you encounter random holes in your mesh")
    enableMapCache: bpy.props.BoolProperty(name="Enable Map Cache", default=True, description="Cache downloaded USGS TNM 3DEP map rasters on disk")
    ccacheSize: bpy.props.IntProperty(name = "Cache Size", default = 50000, min = 0)
    debug_logging_enabled: bpy.props.BoolProperty(name="Enable Logging", default=False, update=logging_settings_update, description="Write TrailPrint3D debug logs to file")
    debug_log_level: bpy.props.EnumProperty(
        name="Log Level",
        items=[
            ("DEBUG", "Debug", "Verbose logging"),
            ("INFO", "Info", "Normal operation logging"),
            ("WARNING", "Warning", "Warnings and errors only"),
            ("ERROR", "Error", "Errors only")
        ],
        default="INFO",
        update=logging_settings_update
    )# type: ignore
    debug_log_filename: bpy.props.StringProperty(name="Log Filename", default="trailprint3d.log", update=logging_settings_update)
    debug_keep_temporary_objects: bpy.props.BoolProperty(
        name="Keep Temporary Objects",
        default=False,
        description="Preserve intermediate/generated temporary geometry for debugging"
    )
    indipendendTiles : bpy.props.BoolProperty(name="IndipendendTiles", default = False, description = "Tile minThickness is indipendend from other tiles")


    sAdditionalExtrusion: bpy.props.FloatProperty(name="sAdditionalExtrusion",default = 0)
    sAutoScale: bpy.props.FloatProperty(name="sAutoScale",default = 1)
    sScaleHor: bpy.props.FloatProperty(name="sScaleHor",default = 1, description = "Scale of the Map")
    sElevationOffset: bpy.props.FloatProperty(name="sElevationOffset", default = 0)
    sMapInKm: bpy.props.FloatProperty(name = "Map Length", default = 0, description = "How much Km are the equivalent of the Map Size")

    col_wActive: bpy.props.BoolProperty(name="Include Water", default=False, description = "Include Water (lakes, ponds) (experimental), Seas dont work yet")
    col_wArea: bpy.props.FloatProperty(name="Water Size Treshold", default = 1, description = "lakes smaller than the treshold wont be included")
    col_ProcessIslands: bpy.props.BoolProperty(name="Process Water Islands", default=True, description="Enable extra island cleanup/repaint logic for water multipolygons")
    col_fActive: bpy.props.BoolProperty(name="Include Forests", default=False, description = "Include Forests (experimental)")
    col_fArea: bpy.props.FloatProperty(name="Forest Size Treshold", default = 10, description = "Forests smaller than the treshold wont be included")
    col_cActive: bpy.props.BoolProperty(name="Include City Boundaries", default=False, description = "Include City Boundaries(experimental)")
    col_cArea: bpy.props.FloatProperty(name="City Size Treshold", default = 1, description = "Cities smaller than the treshold wont be included")
    col_glActive: bpy.props.BoolProperty(name="Include Glaciers", default=False, description = "Include Glaciers (If there are any)")
    col_glArea: bpy.props.FloatProperty(name="Glacier Size Treshold", default = 1, description = "Glaciers smaller than the treshold wont be included")
    col_glMaxRequests: bpy.props.IntProperty(name="Glacier OSM Tile Budget", default = 300, min = 1, max = 5000, description = "Maximum number of OSM tile requests for glaciers before aborting")
    col_KeepManifold: bpy.props.BoolProperty(name="Keep Non-Manifold Objects", default=False, description = "Keep Broken/Non-Manifold Water Parts")
    col_PaintMap: bpy.props.BoolProperty(name="Paint Map", default=True, description = "Paint map instead of Generating Separate Objects (Reccomended for MAC users)")
    col_WaterSpotCleanup: bpy.props.BoolProperty(name="Water Spot Cleanup", default=True, description = "Remove tiny WATER paint spots and optionally fill tiny BASE holes")
    col_WaterSpotCleanupMul: bpy.props.FloatProperty(name="Water Cleanup Threshold Mult", default=2.0, min=0.0, description="Cluster threshold in multiples of median map face area")
    col_WaterHoleFillEnabled: bpy.props.BoolProperty(name="Water Hole Fill", default=False, description="Promote small enclosed BASE holes to WATER during cleanup")
    col_WaterHoleFillMul: bpy.props.FloatProperty(name="Water Hole Fill Mult", default=1.0, min=0.0, description="BASE hole-fill threshold in multiples of median map face area")
    col_WaterMeshNonManifoldEdgeThreshold: bpy.props.IntProperty(name="Water Mesh Non-Manifold Edge Threshold", default=0, min=0, description="Maximum allowed non-manifold edges for water outer meshes before hole carving")

    mountain_treshold:bpy.props.IntProperty(name="Mountain Treshold", default = 60, min = 0, max = 100,subtype='PERCENTAGE', description="Height Treshold to Color Mountians")
    cl_thickness: bpy.props.FloatProperty(name="Contour Line Thickness", default = 0.2, description = "Thickness of the Contour Line")
    cl_distance: bpy.props.FloatProperty(name="Contour Line distance", default = 2, description = "Distance between Contour lines")
    cl_offset: bpy.props.FloatProperty(name="Contour Line offset", default = 0.0, description = "Offset of the Countour lines")

    show_stats: bpy.props.BoolProperty(name="Additional Info", default=False)
    show_coloring: bpy.props.BoolProperty(name="Include Elements", default=False)
    show_chain: bpy.props.BoolProperty(name="Multi Generation", default=False)
    show_map: bpy.props.BoolProperty(name="Map",default=False)
    show_pin: bpy.props.BoolProperty(name="Pin",default=False)
    show_special: bpy.props.BoolProperty(name="Special",default=False)
    show_postProcess: bpy.props.BoolProperty(name="Post Process", default = False)
    show_api: bpy.props.BoolProperty(name="API", default=False)
    show_attribution: bpy.props.BoolProperty(name="Attribution", default = False)
    show_preset: bpy.props.BoolProperty(name="Preset", default=False)

    cityname: bpy.props.StringProperty(name="Cityname", default="Berlin", description = "Get coordinates of a City")
    pinLat: bpy.props.FloatProperty(name="Latitude", default = 48.00)
    pinLon: bpy.props.FloatProperty(name="Longitude", default = 8.00)

    mapmode: bpy.props.EnumProperty(
        name="mapmode",
        items=[
            ('FROMPLANE', "From Plane", "Generate the Map from a Flat Plane"),
            ('FROMCENTER', "From Point", "Generate the Map from a Point coordinate and a Radius"),
            ('2POINTS', "2 Points", "Generate the Map from 2 Coordinates")
        ],
        default='FROMPLANE'
    )# type: ignore

    jMapLat: bpy.props.FloatProperty(name="Latitude", default = 49.00)
    jMapLon: bpy.props.FloatProperty(name="Longitude", default = 9.00)
    jMapRadius: bpy.props.FloatProperty(name="Radius im Km", default = 200)

    jMapLat1: bpy.props.FloatProperty(name="Latitude1", default = 48.00)
    jMapLat2: bpy.props.FloatProperty(name="Latitude2", default = 49.00)
    jMapLon1: bpy.props.FloatProperty(name="Longitude1", default = 8.00)
    jMapLon2: bpy.props.FloatProperty(name="Longitude2", default = 9.00)

    specialBlend_path: bpy.props.StringProperty(
        name="TP3dSpecial.blend Path",
        description="Select the TP3dSpecial.blend file you got from Patreon",
        default="",
        maxlen=1024,
        subtype='FILE_PATH',  # Enables file selection
        #update = update_collection_items
    )# type: ignore

    # Custom property to store selection
    specialCollectionName: bpy.props.EnumProperty(
        name="specialCollection",
        description="Choose a collection from the external .blend",
        items=dynamic_specialCollection_items
    )# type: ignore



    

# Define the operator (script execution)
class MY_OT_runGeneration(bpy.types.Operator):
    bl_idname = "wm.run_my_script"
    bl_label = "Generate"
    bl_description = "Generate the Path and the Map with current Settings"

    def execute(self, context):
        props = context.scene.tp3d  # Access stored variables
        
        runGeneration(0)
        
        return {'FINISHED'}

class MY_OT_ExportSTL(bpy.types.Operator):
    bl_idname = "wm.exportstl"
    bl_label = "Export STL"
    bl_description = "Export Selected Objects as Separate STL (Will lose Colors)"

    def execute(self, context):
        props = context.scene.tp3d  # Access stored variables
        
        global exportPath
        exportPath = bpy.context.scene.tp3d.get('export_path', None)

        if exportPath == None:
            show_message_box("'Export path' is Empty. Please select a Directory For the finished files")
            return {'FINISHED'}
    
        exportPath = bpy.path.abspath(exportPath)

        if not exportPath or exportPath == "":
            show_message_box("Export path is empty! Please select a valid folder.")
            return {'FINISHED'}
        if not os.path.isdir(exportPath):
            show_message_box(f"Invalid export Directory: {exportPath}. Please select a valid Directory.")
            return {'FINISHED'}
        
        if not bpy.context.selected_objects:
            show_message_box("Please select the Object you want to Export")
            return{'FINISHED'}
        
        export_selected_to_STL("STL")

        
        return {'FINISHED'}
    
class MY_OT_ExportOBJ(bpy.types.Operator):
    bl_idname = "wm.exportobj"
    bl_label = "Export OBJ"
    bl_description = "Export Selected Objects as Separate OBJ"

    def execute(self, context):
        props = context.scene.tp3d  # Access stored variables
        
        global exportPath
        exportPath = bpy.context.scene.tp3d.get('export_path', None)

        if exportPath == None:
            show_message_box("'Export path' is Empty. Please select a Directory For the finished files")
            return {'FINISHED'}
    
        exportPath = bpy.path.abspath(exportPath)

        if not exportPath or exportPath == "":
            show_message_box("Export path is empty! Please select a valid folder.")
            return {'FINISHED'}
        if not os.path.isdir(exportPath):
            show_message_box(f"Invalid export Directory: {exportPath}. Please select a valid Directory.")
            return {'FINISHED'}
        
        if not bpy.context.selected_objects:
            show_message_box("Please select the Object you want to Export")
            return{'FINISHED'}
        
        export_selected_to_STL("OBJ")

        
        return {'FINISHED'}

class MY_OT_TestElevationAPI(bpy.types.Operator):
    bl_idname = "wm.test_elevation_api"
    bl_label = "Test Elevation API"
    bl_description = "Run a simple request to verify if the configured elevation server is reachable"

    def execute(self, context):
        props = context.scene.tp3d
        provider = getattr(props, "api_enum", "") or props.api
        lat = props.jMapLat
        lon = props.jMapLon

        if provider == "OPEN-ELEVATION":
            url = "https://api.open-elevation.com/api/v1/lookup"
            payload = {"locations": [{"latitude": lat, "longitude": lon}]}
            try:
                response = requests.post(url, json=payload, timeout=12)
                response.raise_for_status()
                results = response.json().get("results", [])
                elevation = results[0].get("elevation") if results else None
                props.o_elevationApiStatus = f"Status: OK ({response.status_code}) Open-Elevation | elev={elevation}"
            except requests.exceptions.RequestException as e:
                code = getattr(getattr(e, "response", None), "status_code", "no_response")
                props.o_elevationApiStatus = f"Status: ERROR ({code}) Open-Elevation | {str(e)}"
        elif provider == "OPENTOPODATA":
            base = props.selfHosted.strip() if props.selfHosted.strip() else "https://api.opentopodata.org/v1/"
            url = f"{base}{props.dataset}?locations={lat},{lon}"
            try:
                response = requests.get(url, timeout=12)
                response.raise_for_status()
                results = response.json().get("results", [])
                elevation = results[0].get("elevation") if results else None
                props.o_elevationApiStatus = f"Status: OK ({response.status_code}) OpenTopoData | elev={elevation}"
            except requests.exceptions.RequestException as e:
                code = getattr(getattr(e, "response", None), "status_code", "no_response")
                props.o_elevationApiStatus = f"Status: ERROR ({code}) OpenTopoData | {str(e)}"
        elif provider == "USGS_TNM":
            test_lat = 39.7392
            test_lon = -104.9903
            url = f"https://epqs.nationalmap.gov/v1/json?x={test_lon}&y={test_lat}&units=Meters&wkid=4326"
            debug_prefix = f"USGS TNM debug | url={url}"
            print(debug_prefix)
            module_logger.info(debug_prefix)
            try:
                response = requests.get(url, timeout=12, headers=get_usgs_auth_headers())
                response.raise_for_status()
                payload = response.json()
                module_logger.info("USGS TNM debug | status=%s | payload=%s", response.status_code, payload)
                print(f"USGS TNM debug | status={response.status_code} | payload={payload}")
                value = payload.get("value")
                if value is None:
                    value = payload.get("USGS_Elevation_Point_Query_Service", {}).get("Elevation_Query", {}).get("Elevation")
                if value is None:
                    raise ValueError(f"No elevation value found in response: {payload}")
                props.o_elevationApiStatus = f"Status: OK ({response.status_code}) USGS TNM | elev={value}"
            except Exception as e:
                code = getattr(getattr(e, "response", None), "status_code", "no_response")
                module_logger.exception("USGS TNM debug | request failed | code=%s | error=%s", code, str(e))
                print(f"USGS TNM debug | request failed | code={code} | error={str(e)}")
                props.o_elevationApiStatus = f"Status: ERROR ({code}) USGS TNM | {str(e)}"
        else:
            props.o_elevationApiStatus = "Status: Terrain-Tiles uses AWS tile server (no API test endpoint here)"

        self.report({'INFO'}, props.o_elevationApiStatus)
        return {'FINISHED'}


def get_usgs_auth_headers():
    """Build auth headers for USGS requests using a local environment token."""
    token = os.environ.get("USGS_API_TOKEN", "").strip()
    return {"Authorization": f"Bearer {token}"} if token else {}


def open_website(self, context):
    webbrowser.open("https://patreon.com/EmGi3D?utm_source=Blender") 

# Operator to open a website
class MY_OT_OpenWebsite(bpy.types.Operator):
    bl_idname = "wm.open_website"
    bl_label = "Visit My Website"
    bl_description = "The Patreon Version as Additional Features!"

    def execute(self, context):
        open_website(self, context)
        #self.report({'INFO'}, "Opening website...")
        return {'FINISHED'}

def open_discord(self, context):
    webbrowser.open("https://discord.gg/C67H9EJFbz") 

# Operator to open a website
class MY_OT_JoinDiscord(bpy.types.Operator):
    bl_idname = "wm.join_discord"
    bl_label = "Join Discord"
    bl_description = "Discord Community for TrailPrint3D!"

    def execute(self, context):
        open_discord(self, context)
        #self.report({'INFO'}, "Opening website...")
        return {'FINISHED'}
    
class MY_OT_Rescale(bpy.types.Operator):
    bl_idname = "wm.rescale"
    bl_label = "Rescale the z value"
    bl_description = "Rescales the Elevation the Currently selected objects"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        multiZ = bpy.context.scene.tp3d.get('rescaleMultiplier', 1)

        selected_objects = [obj for obj in bpy.context.selected_objects if obj.type in {'MESH', 'CURVE'}]
        lowestZ = 1000

        print("Rescaling")
        for obj in selected_objects:
            if obj.type == 'MESH':
                mesh = obj.data
                for i, vert in enumerate(mesh.vertices):
                    if vert.co.z < lowestZ and vert.co.z > 0.1:
                        lowestZ = vert.co.z
            if obj.type == "CURVE":
                if lowestZ == 1000:
                    for spline in obj.data.splines:
                        for point in spline.bezier_points:
                            if point.co.z > 0.1 and point.co.z < lowestZ:
                                lowestZ = point.co.z

        print(f"lowestZ: {lowestZ}")

        for obj in selected_objects:      
            print(obj.name)
            if lowestZ != 1000 and obj.type == "MESH":
                    bpy.context.view_layer.objects.active = obj  # Make it active
                    bpy.ops.object.mode_set(mode='EDIT')
                    # Access mesh data
                    mesh = bmesh.from_edit_mesh(obj.data)
                    for v in mesh.verts:
                        if v.co.z > 0.1:
                            v.co.z = (v.co.z - lowestZ) * (multiZ) + lowestZ
                    bmesh.update_edit_mesh(obj.data)    
                    bpy.ops.object.mode_set(mode='OBJECT')  # Exit Edit Mode  
            if lowestZ != 1000 and obj.type =="CURVE":
                # Access curve splines
                for spline in obj.data.splines:
                    for point in spline.bezier_points:
                        if point.co.z > -0.5:
                            point.co.z = (point.co.z - lowestZ) * (multiZ) + lowestZ
                    for point in spline.points:  # For NURBS
                        if point.co.z > -0.5:
                            point.co.z = (point.co.z - lowestZ) * (multiZ) + lowestZ

            bpy.ops.object.mode_set(mode='OBJECT')  # Exit Edit Mode

            if "Elevation Scale" in obj:
                obj["Elevation Scale"] *= multiZ

        print(f"Scaled all elevation points by Factor {multiZ} on {len(selected_objects)} object(s).")

        return {'FINISHED'}
    
class MY_OT_savePreset(bpy.types.Operator):
    bl_idname="wm.savepreset"
    bl_label = "Save preset"
    bl_description = "Save the current settings as a preset"
    bl_options = {'REGISTER', 'UNDO'}

    user_input: bpy.props.StringProperty(name="Preset name")

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self)

    def draw(self, context):
        layout = self.layout
        layout.prop(self, "user_input")
    
    def execute(self,context):



        save_myproperties_to_csv(self.user_input)

        show_message_box("Saved Preset","CHECKMARK", " ")

        return {'FINISHED'}

class MY_OT_loadPreset(bpy.types.Operator):
    bl_idname="wm.loadpreset"
    bl_label = "Load preset"
    bl_description = "Load the current settings as a preset"
    bl_options = {'REGISTER', 'UNDO'}
    
    def execute(self,context):
        current = bpy.context.scene.preset_list
        load_myproperties_from_csv(current)

        show_message_box("Preset Loaded","CHECKMARK", " ")

        return {'FINISHED'}

class MY_OT_deletePreset(bpy.types.Operator):
    bl_idname="wm.deletepreset"
    bl_label = "Delete preset"
    bl_description = "Delete the current selected preset"
    bl_options = {'REGISTER', 'UNDO'}
    
    def execute(self,context):
        current = bpy.context.scene.preset_list
        delete_preset_file(current)

        show_message_box("Deleted Selected Preset","CHECKMARK", " ")

        return {'FINISHED'}


class MY_OT_thicken(bpy.types.Operator):
    bl_idname="wm.thicken"
    bl_label = "Thicken Map"
    bl_description = "Make the selected Map thicker"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self,context):
        
        selected_objects = context.selected_objects
        val = bpy.context.scene.tp3d.thickenValue

        bpy.context.tool_settings.mesh_select_mode = (False, False, True)

        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)

        if not selected_objects:
            show_message_box("No objects selected.")
            return {'CANCELLED'}

        for zobj in selected_objects:
            # Check if the custom property 'Object type' exists
            if "Object type" in zobj:
                print(zobj.name)
                if zobj["Object type"] == "TRAIL" or zobj["Object type"] == "WATER" or zobj["Object type"] == "FOREST" or zobj["Object type"] == "CITY":
                    zobj.location.z += val
                elif zobj["Object type"] == "MAP" :
                    zobj.select_set(True)
                    bpy.context.view_layer.objects.active = zobj
                    selectBottomFaces(zobj)
                    bpy.ops.mesh.select_more()
                    bpy.ops.mesh.select_all(action='INVERT')
                    mesh = bmesh.from_edit_mesh(zobj.data)
                    
                    verts_to_move = set()
                    for face in mesh.faces:
                        if face.select:
                            verts_to_move.update(face.verts)

                    for vert in verts_to_move:
                        vert.co.z += val
                    bpy.ops.object.mode_set(mode='OBJECT')
                    bpy.ops.object.select_all(action='DESELECT')
                    zobj.select_set(False)
                    zobj["minThickness"] += val
                    
        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)

                    


        return {'FINISHED'}

class MY_OT_PinCoords(bpy.types.Operator):
    bl_idname="wm.pincoords"
    bl_label = "PinCoords"
    bl_description = "Place a Pin on a Coordinate"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        
        minThickness = bpy.context.scene.tp3d.minThickness

        centerlat = bpy.context.scene.tp3d.pinLat
        centerlon = bpy.context.scene.tp3d.pinLon



        xp,yp,zp = convert_to_blender_coordinates(float(centerlat),float(centerlon),0,0)
        name = "Pin_" + str(round(centerlat,2)) + "." + str(round(centerlon,2))

        #Delete existing object with same name (optional)
        if name in bpy.data.objects:
            bpy.data.objects.remove(bpy.data.objects[name], do_unlink=True)

        #Creatin the Cone
        bpy.ops.mesh.primitive_cone_add(
            vertices=16,
            radius1=0.4,
            radius2=0.8,
            depth=4,
            location=(xp, yp, minThickness + 2)  # Position base at Z=0
        )
        pin = bpy.context.active_object
        pin.name = name

        return {'FINISHED'}

class MY_OT_MagnetHoles(bpy.types.Operator):
    bl_idname = "wm.magnetholes"
    bl_label = "Magnet Holes"
    bl_options = {'REGISTER', 'UNDO'}


    
    def execute(self,context):

        selected_objects = context.selected_objects

        if not selected_objects:
            show_message_box("No objects selected")
            #return{'FINISHED'}
            return{'FINISHED'}
        
        
        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)

        for zobj in selected_objects:

            if zobj.type != 'MESH':
                continue

            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj

            obj_size = bpy.context.scene.tp3d.objSize

            #Check for selection and custom property
            if zobj:
                if "objSize" in zobj.keys():
                    obj_size = zobj["objSize"]
            elif not zobj:
                    print("Select a Map.")
                    return{'FINISHED'}
            
            if "MagnetHoles" not in zobj.keys():
                continue

            if zobj["MagnetHoles"] == True:
                continue

            magnetDiameter = bpy.context.scene.tp3d.magnetDiameter
            magnetHeight = bpy.context.scene.tp3d.magnetHeight

            #Flip normals and Get bottom faces
            selectBottomFaces(zobj)

            #get the lowest zValue of one the faces
            zValue = 0

            # Switch to Edit Mode
            bpy.ops.object.mode_set(mode='EDIT')
            mesh = bmesh.from_edit_mesh(zobj.data)

            # Get the world matrix to convert local to global coordinates
            world_matrix = zobj.matrix_world

            # Collect global Z-values of selected faces
            z_values = [
                (world_matrix @ face.calc_center_median()).z
                for face in mesh.faces if face.select
            ]
            
            zValue = min(z_values)


            bpy.ops.object.mode_set(mode='OBJECT')


            #Set 3D cursor to object's origin
            bpy.context.scene.cursor.location = zobj.location

            #Create 4 cylinders around the object
            radius = obj_size / 3
            angle_step = math.radians(90)
            created_cylinders = []

            for i in range(4):
                angle = i * angle_step
                offset_x = math.cos(angle) * radius
                offset_y = math.sin(angle) * radius
                pos = zobj.location + Vector((offset_x, offset_y, zValue))
                pos = zobj.location + Vector((offset_x, offset_y, 0))

                bpy.ops.mesh.primitive_cylinder_add(
                    radius=magnetDiameter / 2,
                    depth=magnetHeight*2,
                    location=pos
                )
                cyl = bpy.context.active_object
                created_cylinders.append(cyl)

            #Merge cylinders into one object
            bpy.ops.object.select_all(action='DESELECT')
            for cyl in created_cylinders:
                cyl.select_set(True)
            bpy.context.view_layer.objects.active = created_cylinders[0]
            bpy.ops.object.join()
            merged_cylinders = bpy.context.active_object

            #Perform boolean difference
            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj

            bool_mod = zobj.modifiers.new(name="MagnetCutout", type='BOOLEAN')
            bool_mod.operation = 'DIFFERENCE'
            bool_mod.object = merged_cylinders

            bpy.ops.object.modifier_apply(modifier=bool_mod.name)

            #Cleanup - delete the merged cutter object
            bpy.data.objects.remove(merged_cylinders, do_unlink=True)

            zobj["MagnetHoles"] = True

            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(False)

            print("Shlong")

        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)
        

        print("Magnet holes Added")


        return{'FINISHED'}

class MY_OT_Dovetail(bpy.types.Operator):
    bl_idname = "wm.dovetail"
    bl_label = "Dovetail"
    bl_options = {'REGISTER', 'UNDO'}
    
    def execute(self,context):

        selected_objects = context.selected_objects

        if not selected_objects:
            show_message_box("No objects selected")
            return{'FINISHED'}
        
        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)
        
        for zobj in selected_objects:

            if zobj.type != 'MESH':
                continue

            if "Dovetail" not in zobj.keys():
                continue

            if zobj["Dovetail"] == True:
                continue

            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj


            #Check for selection and custom property
            if zobj:
                if "objSize" not in zobj.keys():
                    break
            
            obj_size = zobj["objSize"]
            dovetailSize = 15
            dovetailHeight = 3


            if obj_size <= 50:
                dovetailSize = 5
            elif obj_size <= 75:
                dovetailSize = 10

            #Flip normals and Get bottom faces
            selectBottomFaces(zobj)

            #get the lowest zValue of one the faces
            zValue = 0

            # Switch to Edit Mode
            #bpy.ops.object.mode_set(mode='EDIT')
            mesh = bmesh.from_edit_mesh(zobj.data)

            # Get the world matrix to convert local to global coordinates
            world_matrix = zobj.matrix_world

            # Collect global Z-values of selected faces
            z_values = [
                (world_matrix @ face.calc_center_median()).z
                for face in mesh.faces if face.select
            ]
            
            zValue = min(z_values)

            bpy.ops.object.mode_set(mode='OBJECT')


            #Set 3D cursor to object's origin
            bpy.context.scene.cursor.location = zobj.location

            #Create 4 cylinders around the object
            radius = obj_size/2 * 0.866 - dovetailSize/2
            angle_step = math.radians(60)
            steps = 6
            created_cylinders = []

            for i in range(steps):
                angle = i * angle_step + math.radians(30)
                offset_x = math.cos(angle) * radius
                offset_y = math.sin(angle) * radius
                #pos = zobj.location + Vector((offset_x, offset_y, zValue + dovetailHeight/2))
                pos = zobj.location + Vector((offset_x, offset_y, 0 + dovetailHeight/2))
                rotation = Euler((0, 0, angle - math.radians(90)), 'XYZ')

                bpy.ops.mesh.primitive_cylinder_add(
                    vertices = 3,
                    radius=dovetailSize,
                    depth=dovetailHeight,
                    location=pos,
                    rotation = rotation
                )
                cyl = bpy.context.active_object
                created_cylinders.append(cyl)
        
            #Merge cylinders into one object
            bpy.ops.object.select_all(action='DESELECT')
            for cyl in created_cylinders:
                cyl.select_set(True)
            bpy.context.view_layer.objects.active = created_cylinders[0]
            bpy.ops.object.join()
            merged_cylinders = bpy.context.active_object

            #Select top faces of the Triangles to scale them up slightly
            selectTopFaces(merged_cylinders)

            mesh = bmesh.from_edit_mesh(merged_cylinders.data)
            # Scale factor
            scale_factor = 1.05

            # Scale each selected face from its own center
            for face in mesh.faces:
                if face.select:
                    center = face.calc_center_median()
                    for vert in face.verts:
                        direction = vert.co - center
                        vert.co = center + direction * scale_factor

            # Update the mesh
            bmesh.update_edit_mesh(merged_cylinders.data, loop_triangles=False)

            bpy.ops.object.mode_set(mode='OBJECT')

            #Perform boolean difference
            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj

            bool_mod = zobj.modifiers.new(name="DovetailCutout", type='BOOLEAN')
            bool_mod.operation = 'DIFFERENCE'
            bool_mod.object = merged_cylinders
            

            zobj["Dovetail"] = True

            bpy.ops.object.modifier_apply(modifier=bool_mod.name)

            #Cleanup - delete the merged cutter object
            bpy.data.objects.remove(merged_cylinders, do_unlink=True)

            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(False)
        
        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)


        print("Dovetail Added")


        return{"FINISHED"}

class MY_OT_TerrainDummy(bpy.types.Operator):
    bl_idname = "wm.dummy"
    bl_label = "Dummy Operator"
    def execute(self,context):
        show_message_box("This Feature is Exclusive for Patreon Supporters")
        return{"FINISHED"}
    



class MY_OT_BottomMark(bpy.types.Operator):
    bl_idname = "wm.bottommark"
    bl_label = "Bottom Mark"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self,context):

        selected_objects = context.selected_objects

        bottomMarkCutout = bpy.context.scene.tp3d.bottomMarkCutout

        if not selected_objects:
            show_message_box("No objects selected")
            return{'FINISHED'}
        
        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)

        generated = False
        for zobj in selected_objects:
        
            #Check for selection and custom property
            if "BottomMark" not in zobj.keys():
                continue

            if zobj["BottomMark"] == True:
                continue

            if zobj.type == "MESH" and "objSize" in zobj:

                zobj.select_set(True)
                bpy.context.view_layer.objects.active = zobj

                mark = BottomText(zobj)
                generated = True

                if bottomMarkCutout == True:

                    mark.scale.z = 2

                    recalculateNormals(mark)
                    # Add boolean modifier
                    bool_mod = zobj.modifiers.new(name="Boolean", type='BOOLEAN')
                    bool_mod.object = mark
                    bool_mod.operation = 'DIFFERENCE'
                    bool_mod.solver = 'EXACT'

                    bpy.context.view_layer.objects.active = zobj
                    bpy.ops.object.modifier_apply(modifier=bool_mod.name)

                    bpy.data.objects.remove(mark, do_unlink=True)



                bpy.ops.object.select_all(action='DESELECT')
                zobj.select_set(False)



        
        if generated == False:
            show_message_box("Not a valid Object selected")

        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)



        return{'FINISHED'}
    













    



    


class MY_OT_ColorMountain(bpy.types.Operator):
    bl_idname="wm.colormountain"
    bl_label = "Color Mountains"
    bl_description = "Color Mountains above a certain Treshold"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self,context):

        
        selected_objects = bpy.context.selected_objects
        min_treshold = bpy.context.scene.tp3d.mountain_treshold

        #Collect min/max from custom properties
        min_z = None
        max_z = None
        minThickness = None

        if not selected_objects:
            show_message_box("No Object Selected. Please select a Map first")
            return {'CANCELLED'}

        for obj in selected_objects:
            if "lowestZ" in obj.keys() and "highestZ" in obj.keys() and obj["highestZ"] != 0:
                low = obj["lowestZ"]
                high = obj["highestZ"]
                minThickness = obj["minThickness"]
                min_z = low if min_z is None else min(min_z, low)
                max_z = high if max_z is None else max(max_z, high)

        print(f"Lowest Z across objects: {min_z}, Highest Z: {max_z}")

        #Create or get green material
        matG = bpy.data.materials.get("BASE")
       
        #Create or get a gray material
        mat = bpy.data.materials.get("MOUNTAIN")

        #Iterate objects and faces
        for obj in selected_objects:
            object_type = obj.get("Object type")
            if obj.type != 'MESH' or object_type != "MAP" or max_z in (None, 0):
                print("Not Applied")
                continue
            print("Apply Mountain Color")


            #obj.data.materials.clear()
            #obj.data.materials.append(matG)  # creates first slot and assigns

            bpy.context.view_layer.objects.active = obj
            bpy.ops.object.mode_set(mode='EDIT')
            bm = bmesh.from_edit_mesh(obj.data)

            #Ensure material exists on the object
            matG_index = obj.data.materials.find("BASE")
            mat_index = obj.data.materials.find("MOUNTAIN")
            if mat_index == -1:  # Material not assigned yet
                obj.data.materials.append(mat)
                mat_index = len(obj.data.materials) - 1
            
            tres = (max_z-min_z)/100 * min_treshold + minThickness
            for face in bm.faces:
                #Skip vertical faces (normal is not pointing up/down)
                if abs(face.normal.z) < 0.02:  
                    continue

                avg_z = sum(v.co.z for v in face.verts) / len(face.verts)
                if avg_z > tres and face.material_index == matG_index:
                    face.material_index = mat_index
                elif avg_z < tres and face.material_index == mat_index:
                    face.material_index = matG_index

            bmesh.update_edit_mesh(obj.data)
            bpy.ops.object.mode_set(mode='OBJECT')



        return {'FINISHED'}

class MY_OT_ContourLines(bpy.types.Operator):
    bl_idname="wm.contourlines"
    bl_label = "Contour Lines"
    bl_description = "Color Mountains above a certain Treshold"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self,context):

        
        selected_objects = bpy.context.selected_objects
        cl_thickness = bpy.context.scene.tp3d.cl_thickness
        cl_distance = bpy.context.scene.tp3d.cl_distance
        cl_offset = bpy.context.scene.tp3d.cl_offset

        size = bpy.context.scene.tp3d.objSize



        if not selected_objects:
            show_message_box("No Object Selected. Please select a Map first")
            return {'CANCELLED'}

        for obj in selected_objects:

            if not "Object type" in obj:
                continue
            if obj["Object type"] != "MAP":
                continue

            objs = list(bpy.context.scene.objects)
            for o in objs:
                if "Object type" in o and "PARENT" in o:
                    if o["PARENT"] == obj and  o["Object type"] == "LINES":
                        bpy.data.objects.remove(o, do_unlink=True)
            
            # Deselect everything
            bpy.ops.object.select_all(action='DESELECT')
            
            # Create plane at 3D cursor
            bpy.ops.mesh.primitive_plane_add(size=size + 10, enter_editmode=False, align='WORLD',
                                            location=bpy.context.scene.cursor.location)
            plane = bpy.context.active_object
            plane.name = "CuttingPlane"
            plane.location.z += cl_offset
            
            # Add Array modifier in Z direction
            array_mod = plane.modifiers.new(name="ArrayZ", type='ARRAY')
            array_mod.relative_offset_displace = (0, 0, 0)   # disable relative offset
            array_mod.constant_offset_displace = (0, 0, cl_distance)   # fixed step in Z
            array_mod.use_relative_offset = False
            array_mod.use_constant_offset = True
            array_mod.count = 100  # you can adjust how many slices
            
            # Add Solidify modifier for thickness
            solidify_mod = plane.modifiers.new(name="Solidify", type='SOLIDIFY')
            solidify_mod.thickness = cl_thickness
            
            # Apply modifiers up to solidify
            bpy.context.view_layer.objects.active = plane
            bpy.ops.object.modifier_apply(modifier=array_mod.name)
            bpy.ops.object.modifier_apply(modifier=solidify_mod.name)
            
            # Add Boolean modifier with INTERSECT mode
            bool_mod = plane.modifiers.new(name="Boolean", type='BOOLEAN')
            bool_mod.operation = 'INTERSECT'
            bool_mod.solver = 'MANIFOLD'  # or 'EXACT'
            bool_mod.use_self = False
            bool_mod.use_hole_tolerant = True  # helps with manifold issues
            bool_mod.object = obj

            plane.name = obj.name + "_LINES"

            mat = bpy.data.materials.get("WHITE")
            plane.data.materials.clear()
            plane.data.materials.append(mat)

            writeMetadata(plane,"LINES")
            plane["PARENT"] = obj

            
            # Apply Boolean
            bpy.context.view_layer.objects.active = plane
            
            bpy.ops.object.modifier_apply(modifier=bool_mod.name)



        bpy.ops.object.select_all(action='DESELECT')
        for obj in selected_objects:
            obj.select_set(True)
        bpy.context.view_layer.objects.active = selected_objects[0]
            

        return {'FINISHED'}
    
    
    
# Create the UI Panel
class MY_PT_Generate(bpy.types.Panel):
    bl_label = "Create"
    bl_idname = "PT_EmGi_3DPath+"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "TrailPrint3D"
    

    def draw(self, context):
        layout = self.layout
        props = context.scene.tp3d  # Get properties

        # Add input fields
        layout.operator("wm.open_website",text = "Support me on Patreon", icon='URL')  # Open website
        layout.operator("wm.join_discord",text = "Join Discord", icon='URL')  # Open website
        layout.label(text = "Created by: EmGi, updated by gigamosh57")
        layout.label(text = "Premium Version: 2.52")
        layout.separator()  # Adds a horizontal line
        # Add the script execution button
        layout.label(text = "Create the File")
        layout.operator("wm.run_my_script", icon='DISC')
        box = layout.box()
        box.prop(props, "file_path", icon = "ANIM")
        box.prop(props, "export_path", icon = "FILE_FOLDER")
        box.prop(props, "trailName", icon = "SORTALPHA")
        box.prop(props, "shape")
        box.separator()  # Adds a horizontal line
        box.prop(props, "objSize")
        box.prop(props, "num_subdivisions")
        box.prop(props, "scaleElevation")
        box.prop(props, "pathThickness")
        box.prop(props, "pathRemeshEnabled")
        box.prop(props, "scalemode")
        if props.scalemode == "FACTOR":
            box.prop(props, "pathScale")
        elif props.scalemode == "COORDINATES":
            row = box.row()
            row.prop(props,"scaleLat1")
            row.prop(props,"scaleLon1")
            row = box.row()
            row.prop(props,"scaleLat2")
            row.prop(props,"scaleLon2")
        elif props.scalemode == "SCALE":
            box.prop(props, "pathScale")
        else:
            box.label(text=props.scalemode)

        box.prop(props, "overwritePathElevation") #, icon = "NORMALIZE_FCURVES"

        layout.label(text = props.o_time, icon = "TIME")
        layout.label(text = "------------------------------")
        

class MY_PT_Advanced(bpy.types.Panel):
    bl_label = "Advanced"
    bl_idname = "PT_Advanced"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "TrailPrint3D"
    
    def draw(self, context):
        layout = self.layout
        props = context.scene.tp3d  # Get properties
        
        #Add input fields

        #STL EXPORT
        box = layout.box()
        box.label(text = "Manually export selected to STL/OBJ")
        box.operator("wm.exportstl", icon="EXPORT")
        box.operator("wm.exportobj", icon = "EXPORT")

        log_box = layout.box()
        log_box.label(text="Logging")
        log_box.prop(props, "debug_logging_enabled", text="Enable/Disable Logging", toggle=True)
        log_box.prop(props, "debug_keep_temporary_objects", text="Keep Temporary Objects", toggle=True)
        if props.debug_keep_temporary_objects:
            warn_row = log_box.row()
            warn_row.label(text="Warning: Keeping temporary objects may clutter the scene.", icon="ERROR")
        if props.debug_logging_enabled:
            log_box.prop(props, "debug_log_level")
            log_box.prop(props, "debug_log_filename")
            log_box.operator("wm.open_log_folder", icon="FILE_FOLDER")


        #MAP
        layout.prop(props,"show_map", icon="TRIA_DOWN" if props.show_map else "TRIA_RIGHT", emboss=True)
        if props.show_map:
            box = layout.box()
            box.prop(props, "fixedElevationScale")
            box.prop(props, "minThickness")
            box.prop(props, "shapeRotation")
            box.prop(props, "xTerrainOffset")
            box.prop(props, "yTerrainOffset")
            box.prop(props, "singleColorMode")
            box.prop(props, "tolerance")
            box.prop(props, "disableCache")
            box.prop(props, "enableMapCache")
            box.prop(props, "ccacheSize")
            box.separator()  # Adds a horizontal line
            box.separator()  # Adds a horizontal line

            box.label(text="Custom Maps")
            if bpy.context.scene.tp3d.sScaleHor != None and category == "TrailPrint3D+":
                box.prop(props, "mapmode")
                if props.mapmode == "FROMPLANE":
                    box.operator("wm.terrain", text = "Create Map from selected", icon = "OBJECT_DATA")
                    box.prop(props,"indipendendTiles")
                    box.separator()
                    #Create Blank
                    box.operator("wm.create_blank", text = "Create Blank", icon = "SNAP_FACE")
                    box.operator("wm.extend_tile", text = "Extend Selected Tile", icon = "SELECT_EXTEND")
                    box.prop(props,"tileSpacing")
                elif props.mapmode == "FROMCENTER":
                    row = box.row()
                    row.prop(props, "jMapLat")
                    row.prop(props, "jMapLon")
                    box.prop(props, "jMapRadius")
                    box.operator("wm.fromcentergeneration", text = "Create Map from 1 Point + Radius")
                    box.operator("wm.fromcentergenerationwithtrail", text = "Create Map with Trail from 1 Point + Radius")

                elif props.mapmode == "2POINTS":
                    row = box.row()
                    row.prop(props, "jMapLat1")
                    row.prop(props, "jMapLon1")
                    row = box.row()
                    row.prop(props, "jMapLat2")
                    row.prop(props, "jMapLon2")
                    box.operator("wm.2pointgeneration", text = "Create Map from 2 Points")
                else:
                    box.label(text=props.scalemode)
                
                box.separator()
                #Merge with Map
                box.operator("wm.mergewithmap",text ="Merge with Map", icon = "AUTOMERGE_OFF")
                box.operator("wm.justtrail", text = "Generate Just Trail", icon = "DECORATE_DRIVER")
            

                box.separator()  # Adds a horizontal line
            elif bpy.context.scene.tp3d.sScaleHor != None and category == "TrailPrint3D+":
                box.label(text = "Only works after Generating a map")
                box.label(text = "(same Session)")
            else:
                box.operator("wm.dummy", text = "Create Map from selected", icon = "LOCKED")
                box.operator("wm.dummy",text ="Merge with Map", icon = "LOCKED")
                box.operator("wm.dummy", text = "Create Blank", icon = "LOCKED")
                

            layout.separator()  # Adds a horizontal line

        #MULTI
        if category == "TrailPrint3D+":
            layout.prop(props,"show_chain", icon="TRIA_DOWN" if props.show_chain else "TRIA_RIGHT", emboss=True)
            if props.show_chain:
                box = layout.box()
                box.label(text = "MULTI GENERATION")
                box.label(text = "Create a Single map out of a Folder of GPX files")
                box.prop(props, "chain_path")
                box.operator("wm.run_my_script2", icon = "OUTLINER_DATA_CURVES")
                layout.separator()  # Adds a horizontal line
        else:
            layout.prop(props,"show_chain", icon = "LOCKED", emboss = True)
            if props.show_chain:
                box = layout.box()
                box.label(text = "Exclusive for Patreon Supporters")
                box.label(text= "- Create Maps with multiple Trails on it")
                box.label(text= "- Chain together multiple Trails (e.G from Multi-Day trips)")
                layout.separator()  # Adds a horizontal line
            

        #INCLUDE ELEMENTS
        layout.prop(props,"show_coloring", icon="TRIA_DOWN" if props.show_coloring else "TRIA_RIGHT", emboss=True)
        if props.show_coloring:
            boxer = layout.box()
            box = boxer.box()
            box.label(text = "Water")
            box.prop(props, "col_wActive")
            box.prop(props, "col_wArea")
            box.prop(props, "col_ProcessIslands")
            box = boxer.box()
            box.label(text = "Forests")
            box.prop(props, "col_fActive")
            box.prop(props, "col_fArea")
            box = boxer.box()
            box.label(text = "City Boundaries")
            box.prop(props, "col_cActive")
            box.prop(props, "col_cArea")
            box = boxer.box()
            box.label(text = "Glaciers")
            box.prop(props, "col_glActive")
            box.prop(props, "col_glArea")
            box.prop(props, "col_glMaxRequests")

            #layout.prop(props, "col_KeepManifold")
            boxer.prop(props,"col_PaintMap")
            if props.col_wActive and props.col_PaintMap:
                boxer.prop(props, "col_WaterSpotCleanup")
                if props.col_WaterSpotCleanup:
                    boxer.prop(props, "col_WaterSpotCleanupMul")
                    boxer.prop(props, "col_WaterHoleFillEnabled")
                    if props.col_WaterHoleFillEnabled:
                        boxer.prop(props, "col_WaterHoleFillMul")
            
        
        #PIN
        layout.prop(props,"show_pin", icon="TRIA_DOWN" if props.show_pin else "TRIA_RIGHT", emboss=True)
        if props.show_pin:
            box = layout.box()
            box.label(text="Set pin by Coordinates")
            row = box.row()
            row.prop(props, "pinLat")
            row.prop(props, "pinLon")
            box.operator("wm.pincoords", text = "Pin on Coords", icon = "PINNED")
            box.separator()  # Adds a horizontal line
            if category == "TrailPrint3D+":
                box.label(text="Set pin by Cityname")
                box.prop(props, "cityname")
                box.operator("wm.citycoords",text = "Pin on City", icon = "UNPINNED")
            else:
                box.prop(props, "cityname")
                box.operator("wm.dummy",text = "Pin on City", icon = "LOCKED" )
        
        #SPECIAL
        if category == "TrailPrint3D+":
            layout.prop(props,"show_special",icon="TRIA_DOWN" if props.show_special else "TRIA_RIGHT", emboss = True)
            if props.show_special:
                box = layout.box()
                box.prop(props, "specialBlend_path")
                box.operator("wm.update_special_collection", text = "Load .blend File", icon = "BLENDER")
                box.prop(props, "specialCollectionName", text="Collection")
                box.operator("wm.appendcollection", text = "Import", icon = "IMPORT")
        else:
            layout.prop(props,"show_special", icon = "LOCKED", emboss = True)
            if props.show_special:
                box = layout.box()
                box.label(text = "Exclusive for Patreon Supporters")
                box.label(text= "- Use Special Manual crafted Handtemplates")
                box.label(text= "- e.G Jigzaw Puzzle, Sliding Puzzle of your Map")
                layout.separator()  # Adds a horizontal line
        
        #POST PROCESS
        layout.prop(props,"show_postProcess", icon = "TRIA_DOWN" if props.show_postProcess else "TRIA_RIGHT", emboss = True)
        if props.show_postProcess:
            box = layout.box()
            box.label(text = "Manually export object after these actions")
            box.separator()
            box.label(text="Color Mountains")
            box.prop(props,"mountain_treshold")
            box.operator("wm.colormountain", text = "Color Mountains", icon = "RNDCURVE")
            box.separator()

            box.prop(props,"cl_thickness")
            box.prop(props,"cl_distance")
            box.prop(props,"cl_offset")
            box.operator("wm.contourlines", icon = "ALIGN_JUSTIFY")

            box.separator()

            box.label(text="Rescale the Elevation of selected Objects")
            row = box.row()
            row.prop(props, "rescaleMultiplier")
            row.operator("wm.rescale",text = "Rescale Elevation" )
            box.separator()  # Adds a horizontal line

            box.label(text = "Extrude the Terrain of selected Object by a value")
            box.prop(props,"thickenValue")
            box.operator("wm.thicken", text = "Extrude Terrain", icon = "EMPTY_SINGLE_ARROW")
            box.separator()

            row = box.row()
            row.prop(props,"magnetHeight")
            row.prop(props,"magnetDiameter")
            box.operator("wm.magnetholes", text = "Add Magnet Holes", icon = "SNAP_OFF")

            box.separator()
            box.operator("wm.dovetail", text = "Add Dovetail Cutouts", icon = "SHAPEKEY_DATA")

            box.separator()
            box.operator("wm.bottommark", text = "Add Bottom Mark", icon = "SMALL_CAPS")
            box.prop(props,"bottomMarkCutout")
        

        layout.prop(props,"show_preset", icon="TRIA_DOWN" if props.show_preset else "TRIA_RIGHT", emboss=True)
        if props.show_preset:
            box = layout.box()
            box.prop(context.scene, "preset_list")
            box.operator("wm.loadpreset", icon = "PRESET")
            row = box.row()
            row.operator("wm.savepreset", icon = "PRESET_NEW")
            row.operator("wm.deletepreset", icon = "REMOVE")


        #API
        layout.prop(props,"show_api", icon="TRIA_DOWN" if props.show_api else "TRIA_RIGHT", emboss=True)
        if props.show_api:
            box = layout.box()
            box.prop(props,"api", icon = "INTERNET")
            box.operator("wm.test_elevation_api", icon="URL")
            box.label(text=props.o_elevationApiStatus)
            if props.api == "OPENTOPODATA":
                box.prop(props, "dataset")
                box.separator()  # Adds a horizontal line
                box.label(text="If you hosted your own Version of Opentopodata:")
                box.prop(props, "selfHosted")
                layout.separator()  # Adds a horizontal line

        #STATS
        layout.prop(props,"show_stats", icon="TRIA_DOWN" if props.show_stats else "TRIA_RIGHT", emboss=True)
        if props.show_stats:
            box = layout.box()
            box.label(text="Get Input Settings of Selected Generate Map")
            box.operator("object.show_custom_props_popup", icon = "QUESTION")
            box = layout.box()
            box.label(text = props.o_verticesPath)
            box.label(text = props.o_verticesMap)
            box.label(text = props.o_mapScale)
            box.label(text = f"scaleHor: {props.sScaleHor}")
            box.label(text = f"Map Size: {props.sMapInKm}")
            box.label(text = props.o_time)
            box.separator()  # Adds a horizontal line
            box.label(text = "Opentopodata:")
            box.label(text = props.o_apiCounter_OpenTopoData)
            box.label(text = "OpenElevation:")
            box.label(text = props.o_apiCounter_OpenElevation)
            layout.separator()  # Adds a horizontal line

        #ATTRIBUTION
        layout.prop(props,"show_attribution", icon="TRIA_DOWN" if props.show_attribution else "TRIA_RIGHT", emboss=True)
        if props.show_attribution:
            box = layout.box()
            box.label(text = "Attribution")
            box.label(text = "Elevation data from OpenTopoData, using the SRTM and other datasets.")
            box.label(text = "Elevation data from Open-Elevation, based on Shuttle Radar Topography Mission (SRTM) data © NASA.")
            box.label(text = "Elevation data from USGS TNM, The National Map elevation query service (USGS).")
            box.label(text = "Water, Forests, City data © OpenStreetMap contributors")
            box.label(text = "Terrain data from Mapzen, based on data © OpenStreetMap contributors, NASA SRTM, and USGS.")
            layout.separator()  # Adds a horizontal line

class MY_PT_Shapes(bpy.types.Panel):
    bl_label = "Additional Shape Settings"
    bl_idname = "PT_ShapeSettings"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "TrailPrint3D"
    
    def draw(self, context):
        layout = self.layout
        props = context.scene.tp3d  # Get properties
        
        #print(f"shape: {props.shape}")
        if props.shape == "HEXAGON INNER TEXT" or props.shape == "HEXAGON OUTER TEXT" or props.shape == "OCTAGON OUTER TEXT" or props.shape == "HEXAGON FRONT TEXT":

            #Add input fields
            layout.prop(props, "textFont")
            layout.prop(props, "textSize")
            layout.prop(props, "textSizeTitle")
            layout.separator()  # Adds a horizontal line
            layout.label(text = "Overwrite text:")
            layout.prop(props, "overwriteLength")
            layout.prop(props, "overwriteHeight")
            layout.prop(props, "overwriteTime")
            layout.prop(props, "plateThickness")
            layout.prop(props, "outerBorderSize")
            layout.prop(props, "plateInsertValue")
            layout.prop(props, "text_angle_preset")


class OBJECT_OT_ShowCustomPropsPopup(bpy.types.Operator):
    bl_idname = "object.show_custom_props_popup"
    bl_label = "Generation Settings"
    bl_description = "Show what Settings were used to Generate this Object (With Map object Selected)"
    bl_options = {'REGISTER'}

    MAX_PER_COLUMN = 25
    NORMAL_WIDTH = 400
    DOUBLE_WIDTH = 800

    def draw(self, context):
        layout = self.layout
        obj = context.active_object

        if not obj:
            layout.label(text="No active object.", icon="ERROR")
            return

        custom_props = [k for k in obj.keys() if not k.startswith("_")]

        if not custom_props:
            layout.label(text="No custom properties found. Please Select a Map", icon="INFO")
            return

        total = len(custom_props)

        if total > self.MAX_PER_COLUMN:
            split = layout.split(factor=0.5)
            col1 = split.column(align=True)
            col2 = split.column(align=True)

            mid = (total + 1) // 2

            for col, chunk in zip((col1, col2), (custom_props[:mid], custom_props[mid:])):
                for key in chunk:
                    row = col.row()
                    row.label(text=key + ":", icon='DOT')
                    row.label(text=str(obj[key]))
        else:
            col = layout.column(align=True)
            for key in custom_props:
                row = col.row()
                row.label(text=key + ":", icon='DOT')
                row.label(text=str(obj[key]))

    def execute(self, context):
        return {'FINISHED'}

    def invoke(self, context, event):
        obj = context.active_object
        custom_props = [k for k in obj.keys() if not k.startswith("_")] if obj else []
        width = self.DOUBLE_WIDTH if len(custom_props) > self.MAX_PER_COLUMN else self.NORMAL_WIDTH
        return context.window_manager.invoke_props_dialog(self, width=width)


class MY_OT_OpenLogFolder(bpy.types.Operator):
    bl_idname = "wm.open_log_folder"
    bl_label = "Open Log Folder"
    bl_description = "Open folder where TrailPrint3D logs are written"

    def execute(self, context):
        props = context.scene.tp3d
        folder = _resolve_log_folder(props)
        try:
            webbrowser.open(folder)
            return {'FINISHED'}
        except Exception as e:
            module_logger.exception("Failed to open log folder: %s", folder)
            show_message_box(f"Failed to open log folder: {e}")
            return {'CANCELLED'}

# Register the classes and properties
def register():
    bpy.utils.register_class(MyProperties)
    bpy.types.Scene.tp3d = bpy.props.PointerProperty(type=MyProperties)

    bpy.utils.register_class(MY_OT_runGeneration)
    bpy.utils.register_class(MY_OT_ExportSTL)
    bpy.utils.register_class(MY_OT_ExportOBJ)
    bpy.utils.register_class(MY_OT_TestElevationAPI)
    bpy.utils.register_class(MY_PT_Generate)
    bpy.utils.register_class(MY_PT_Advanced)
    bpy.utils.register_class(MY_OT_OpenWebsite)
    bpy.utils.register_class(MY_OT_JoinDiscord)
    bpy.utils.register_class(MY_OT_Rescale)
    bpy.utils.register_class(MY_OT_OpenLogFolder)
    bpy.utils.register_class(OBJECT_OT_ShowCustomPropsPopup)
    bpy.utils.register_class(MY_OT_PinCoords)
    bpy.utils.register_class(MY_OT_TerrainDummy)
    bpy.utils.register_class(MY_OT_MagnetHoles)
    bpy.utils.register_class(MY_OT_Dovetail)
    bpy.utils.register_class(MY_OT_thicken)
    bpy.utils.register_class(MY_OT_BottomMark)
    bpy.utils.register_class(MY_OT_ColorMountain)
    bpy.utils.register_class(MY_OT_ContourLines)
    bpy.utils.register_class(MY_OT_savePreset)
    bpy.utils.register_class(MY_OT_loadPreset)
    bpy.utils.register_class(MY_OT_deletePreset)



    


def unregister():
    del bpy.types.Scene.tp3d
    bpy.utils.unregister_class(MyProperties)

    bpy.utils.unregister_class(MY_OT_runGeneration)
    bpy.utils.unregister_class(MY_OT_ExportSTL)
    bpy.utils.unregister_class(MY_OT_ExportOBJ)
    bpy.utils.unregister_class(MY_OT_TestElevationAPI)
    bpy.utils.unregister_class(MY_PT_Generate)
    bpy.utils.unregister_class(MY_PT_Advanced)
    bpy.utils.unregister_class(MY_OT_OpenWebsite)
    bpy.utils.unregister_class(MY_OT_JoinDiscord)
    bpy.utils.unregister_class(MY_OT_Rescale)
    bpy.utils.unregister_class(MY_OT_OpenLogFolder)
    bpy.utils.unregister_class(OBJECT_OT_ShowCustomPropsPopup)
    bpy.utils.unregister_class(MY_OT_PinCoords)
    bpy.utils.unregister_class(MY_OT_TerrainDummy)
    bpy.utils.unregister_class(MY_OT_MagnetHoles)
    bpy.utils.unregister_class(MY_OT_Dovetail)
    bpy.utils.unregister_class(MY_OT_thicken)
    bpy.utils.unregister_class(MY_OT_BottomMark)
    bpy.utils.unregister_class(MY_OT_ColorMountain)
    bpy.utils.unregister_class(MY_OT_ContourLines)
    bpy.utils.unregister_class(MY_OT_savePreset)
    bpy.utils.unregister_class(MY_OT_loadPreset)
    bpy.utils.unregister_class(MY_OT_deletePreset)





#--------------------------------------------------
#Debug
#--------------------------------------------------


def save_myproperties_to_csv(filename):
    """
    Save all writable properties of a MyProperties instance to a CSV file.
    Each row is: property_name , value
    """
    folder = os.path.join(bpy.utils.user_resource('CONFIG'), "presets")
    os.makedirs(folder, exist_ok=True)

    filepath = os.path.join(folder, filename + ".csv")

    props = bpy.context.scene.tp3d

    print(filepath)

    with open(filepath, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["property", "value"])  # header

        for p in props.bl_rna.properties:
            name = p.identifier
            if name == "rna_type" or p.is_readonly:
                continue

            try:
                value = getattr(props, name)
            except:
                continue

            # Convert lists/tuples to string
            if isinstance(value, (list, tuple)):
                value = ",".join(map(str, value))

            writer.writerow([name, value])

def load_myproperties_from_csv(filename):
    """
    Load all properties from a CSV file and overwrite the values in MyProperties.
    """
    folder = os.path.join(bpy.utils.user_resource('CONFIG'), "presets")
    filepath = os.path.join(folder, filename + ".csv")

    if not os.path.isfile(filepath):
        print("Preset file not found:", filepath)
        return

    props = bpy.context.scene.tp3d

    with open(filepath, "r", encoding="utf-8") as f:
        reader = csv.reader(f)
        next(reader)  # skip header

        for row in reader:
            if len(row) < 2:
                continue

            name, value = row[0], row[1]

            if not hasattr(props, name):
                continue  # skip unknown properties

            current = getattr(props, name)

            try:
                # Convert back to correct type
                if isinstance(current, bool):
                    value = value.lower() == "true"

                elif isinstance(current, int):
                    value = int(value)

                elif isinstance(current, float):
                    value = float(value)

                elif isinstance(current, (list, tuple)):
                    # Split list stored as comma-separated string
                    value = [float(v) for v in value.split(",")]

                # strings stay strings
            except:
                # Failed conversion → keep original
                continue

            try:
                setattr(props, name, value)
            except:
                pass

def delete_preset_file(preset_name):
    """
    Deletes a preset .csv file from the Blender CONFIG/presets folder.
    preset_name = name WITHOUT extension
    """
    folder = os.path.join(bpy.utils.user_resource('CONFIG'), "presets")
    filepath = os.path.join(folder, preset_name + ".csv")

    if not os.path.isfile(filepath):
        print("File not found:", filepath)
        return False

    try:
        os.remove(filepath)
        print("Deleted:", filepath)
        return True
    except Exception as e:
        print("Error deleting file:", e)
        return False

        
def list_files_callback(self, context):
    folder = os.path.join(bpy.utils.user_resource('CONFIG'), "presets")
    items = []

    if os.path.isdir(folder):
        for fname in os.listdir(folder):
            if os.path.isfile(os.path.join(folder, fname)):
                name_no_ext = os.path.splitext(fname)[0]
                items.append((name_no_ext, name_no_ext, ""))

    # Show placeholder if empty
    if not items:
        items.append(("none", "-- No files found --", ""))

    return items

bpy.types.Scene.preset_list = bpy.props.EnumProperty(
    name="Presets",
    items=list_files_callback
)

def load_counter():
    if os.path.exists(counter_file):
        try:
            with open(counter_file, "r") as f:
                data = json.load(f)
                return data.get("count_openTopodata", 0), data.get("date_openTopoData", ""), data.get("count_openElevation",0), data.get("date_openElevation","")
        except:
            return 0, "", 0, ""
    return 0, "", 0, ""

# Function to save the counter data
def save_counter(count_openTopodata, date_openTopoData, count_openElevation, date_openElevation):
    with open(counter_file, "w") as f:
        json.dump({"count_openTopodata": count_openTopodata, "date_openTopoData": date_openTopoData, "count_openElevation": count_openElevation, "date_openElevation": date_openElevation}, f)

# Function to update the request counter
def update_request_counter():
    today = date.today().isoformat()  # ✅ This correctly gets today's date
    today_date = date.today().isoformat()  # Get today's date in iso format
    today_month = date.today().month  # Get current month as an integer (1-12)
    count_openTopodata, date_openTopoData, count_openElevation, date_openElevation = load_counter()

    # Reset counter if the date has changed
    if date_openTopoData != today_date:
        count_openTopodata = 0
    
    if date_openElevation != today_month:
        count_openElevation = 0

    global api
    if api == 0:
        count_openTopodata += 1
    elif api == 1:
        count_openElevation += 1

    save_counter(count_openTopodata, today_date, count_openElevation,today_month)
    
    return count_openTopodata, count_openElevation  # Return the updated count

@log_workflow
def send_api_request(addition = ""):
    
    global dataset
    request_count = update_request_counter()
    now = datetime.now()
    if api == 0:
        module_logger.info("%02d:%02d | Fetching: %s | API Usage: %s | %s", now.hour, now.minute, addition, request_count, dataset)
    elif api == 1:
        module_logger.info("%02d:%02d | Fetching: %s | API Usage: %s", now.hour, now.minute, addition, request_count)
    elif api == 2:
        module_logger.info("%02d:%02d | Fetching API", now.hour, now.minute)
    
if __name__ == "__main__":
    
    register()
    #unregister()


#--------------------------------------------------------------------------------------------------------------------
#DISPLAY GENERATION----------------------------------------------------------------------------------------------------------
#--------------------------------------------------------------------------------------------------------------------

import xml.etree.ElementTree as ET
from datetime import datetime
import bpy

@log_workflow
def read_gpx_1_1(filepath):
    """
    Reads a GPX file and extracts the coordinates, elevation, and timestamps
    from either track points (trkpt) or route points (rtept).
    """

    tree = ET.parse(filepath)
    root = tree.getroot()

    segmentlist = []
    # Define namespaces for parsing GPX
    ns = {'default': 'http://www.topografix.com/GPX/1/1'}

    #find segments inside the file
    ammount = 0
    segments = root.findall('.//default:trkseg',ns)
    module_logger.info("read_gpx_1_1 segments=%s filepath=%s", len(segments), filepath)
    if segments:
        for seg in segments:
            # Try to find track points first
            points = seg.findall('.//default:trkpt', ns)
            point_type = 'trkpt'

            # If no track points found, look for route points
            if not points:
                points = seg.findall('.//default:rtept', ns)
                point_type = 'rtept'

            segcoords = []
            lowestElevation = 10000

            for pt in points:
                lat = float(pt.get('lat'))
                lon = float(pt.get('lon'))
                ele = pt.find('default:ele', ns)
                elevation = float(ele.text) if ele is not None else 0.0
                time = pt.find('default:time', ns)
                ammount += 1
                try:
                    timestamp = datetime.fromisoformat(time.text.replace("Z", "+00:00")) if time is not None else None
                except Exception:
                    timestamp = None
                segcoords.append((lat, lon, elevation, timestamp))
                if elevation < lowestElevation:
                    lowestElevation = elevation

            global elevationOffset
            elevationOffset = max(lowestElevation - 50, 0)

            bpy.context.scene.tp3d["sElevationOffset"] = elevationOffset
            bpy.context.scene.tp3d["o_verticesPath"] = f"{point_type.upper()}  Path vertices: {len(segcoords)}"
            segmentlist.append(segcoords)

    #coordinates.append(segcoords)
    module_logger.info("read_gpx_1_1 points=%s", ammount)
    return segmentlist





@log_workflow
def read_gpx_1_0(filepath):
    """Reads a GPX 1.0 file and extracts the coordinates, elevation, and timestamps."""
    tree = ET.parse(filepath)
    root = tree.getroot()
    
    segmentlist = []
    # Define the namespace to handle the GPX 1.0 format correctly
    ns = {'gpx': 'http://www.topografix.com/GPX/1/0'}

    # Extract track points (latitude, longitude, elevation, timestamp)
    segcoords = []
    lowestElevation = 10000

    segments = root.findall('.//gpx:trkseg',ns)
    module_logger.info("read_gpx_1_0 segments=%s filepath=%s", len(segments), filepath)
    
                        
    if segments:
        for seg in segments:
            # Extracting track points
            for trkpt in seg.findall('.//gpx:trkpt', ns):
                lat = float(trkpt.get('lat'))
                lon = float(trkpt.get('lon'))
                ele = trkpt.find('gpx:ele', ns)
                elevation = float(ele.text) if ele is not None else 0.0
                time = trkpt.find('gpx:time', ns)
                timestamp = datetime.fromisoformat(time.text) if time is not None else None
                #print(f"lat: {lat}, long: {lon}, ele: {elevation}, time: {timestamp}")
                segcoords.append((lat, lon, elevation, timestamp))
                
                if elevation < lowestElevation:
                    lowestElevation = elevation
            
            global elevationOffset
            elevationOffset = max(lowestElevation - 50, 0)

            bpy.context.scene.tp3d["sElevationOffset"] = elevationOffset
            
            bpy.context.scene.tp3d["o_verticesPath"] = f"Path vertices: {len(segcoords)}"
            segmentlist.append(segcoords)
            
    return segmentlist

@log_workflow
def read_igc(filepath):
    """Reads an IGC file and extracts the coordinates, elevation, and timestamps."""
    segmentlist = []
    coordinates = []
    lowestElevation = 10000
    
    with open(filepath, 'r') as file:
        for line in file:
            # IGC B records contain position data
            if line.startswith('B'):
                try:
                    # Extract time (HHMMSS)
                    time_str = line[1:7]
                    hours = int(time_str[0:2])
                    minutes = int(time_str[2:4])
                    seconds = int(time_str[4:6])
                    
                    # Extract latitude (DDMMmmmN/S)
                    lat_str = line[7:15]
                    lat_deg = int(lat_str[0:2])
                    lat_min = int(lat_str[2:4])
                    lat_min_frac = int(lat_str[4:7]) / 1000.0
                    lat = lat_deg + (lat_min + lat_min_frac) / 60.0
                    if lat_str[7] == 'S':
                        lat = -lat
                    
                    # Extract longitude (DDDMMmmmE/W)
                    lon_str = line[15:24]
                    lon_deg = int(lon_str[0:3])
                    lon_min = int(lon_str[3:5])
                    lon_min_frac = int(lon_str[5:8]) / 1000.0
                    lon = lon_deg + (lon_min + lon_min_frac) / 60.0
                    if lon_str[8] == 'W':
                        lon = -lon
                    
                    # Extract pressure altitude (in meters)
                    pressure_alt = int(line[25:30])
                    
                    # Extract GPS altitude (in meters)
                    gps_alt = int(line[30:35])
                    
                    # Create timestamp (using current date since IGC files don't store date in B records)
                    now = datetime.now()
                    timestamp = datetime(now.year, now.month, now.day, hours, minutes, seconds)
                    
                    # Use GPS altitude for elevation
                    elevation = gps_alt
                    
                    coordinates.append((lat, lon, elevation, timestamp))
                    
                    if elevation < lowestElevation:
                        lowestElevation = elevation
                        
                except (ValueError, IndexError) as e:
                    module_logger.warning("IGC parse error in %s line=%s", filepath, line.strip())
                    continue
    
    global elevationOffset
    elevationOffset = max(lowestElevation - 50, 0)
    
    bpy.context.scene.tp3d["o_verticesPath"] = "Path vertices: " + str(len(coordinates))

    segmentlist.append(coordinates)
    return segmentlist


@log_workflow
def read_gpx_directory(directory_path):
    """Reads all GPX files in a directory and extracts coordinates, elevation, and timestamps."""
    
    # Define GPX namespace
    ns = {'default': 'http://www.topografix.com/GPX/1/1'}
    
    # List to store all coordinates from all GPX files
    coordinates = []
    coordinatesSeparate = []  # Stores a list of lists for separate files
    lowestElevation = 10000  # High initial value

    # Iterate over all files in the directory
    for filename in os.listdir(directory_path):
        if filename.lower().endswith(".gpx"):  # Only process .gpx files
            filepath = os.path.join(directory_path, filename)

            file_extension = os.path.splitext(filepath)[1].lower()
            if file_extension == '.gpx':
                tree = ET.parse(filepath)
                root = tree.getroot()
                version = root.get("version")
                module_logger.info("Processing GPX file=%s version=%s", filename, version)
                if version == "1.0":
                    co= read_gpx_1_0(filepath)
                if version == "1.1":
                    co= read_gpx_1_1(filepath)
            elif file_extension == '.igc':
                co= read_igc(filepath)

            # Append the file-specific list to coordinatesSeparate
            if co:
                for coseg in co:
                    coordinatesSeparate.append(coseg)
                    lowest = min(coseg, key = lambda x: x[2])
                    lowest_In_coords = lowest[2]
                    if lowest_In_coords < lowestElevation:
                        lowestElevation = lowest_In_coords
                        print(f"new Lowest Elevation: {lowestElevation}")
            
    #Merge the separate coordinates to one big list together
    coordinates = [pt for sublist in coordinatesSeparate for pt in sublist]
    

    # Calculate elevation offset
    global elevationOffset
    elevationOffset = max(lowestElevation - 50, 0)

    bpy.context.scene.tp3d["sElevationOffset"] = elevationOffset

    # Store the number of points in the Blender scene property
    bpy.context.scene.tp3d["o_verticesPath"] = f"Path vertices: {len(coordinates)}"
    
    print(f"Total GPX files processed: {len(coordinatesSeparate)}")
    
    return coordinatesSeparate

def read_gpx_file():

    gpx_file_path = bpy.context.scene.tp3d.get('file_path', None)

    coords = []
    file_extension = os.path.splitext(gpx_file_path)[1].lower()
    if file_extension == '.gpx':
        tree = ET.parse(gpx_file_path)
        root = tree.getroot()
        version = root.get("version")

        ns = {'default': root.tag.split('}')[0].strip('{')}
        global GPXsections
        GPXsections = len(root.findall(".//default:trkseg", ns))
        print(f"GPX Sections: {GPXsections}")
        
        if version == "1.0":
            coords = read_gpx_1_0(gpx_file_path)
        if version == "1.1":
            coords= read_gpx_1_1(gpx_file_path)
    elif file_extension == '.igc':
        coords= read_igc(gpx_file_path)
    else:
        show_message_box("Unsupported file format. Please use .gpx or .igc files.")
        toggle_console()
        return

    print(f"poats: {len(coords)}")
    
    return coords
    

# Load cache from disk
def load_elevation_cache():
    """Load the elevation cache from disk"""

    global _elevation_cache
    if os.path.exists(elevation_cache_file):
        try:
            with open(elevation_cache_file, "r") as f:
                _elevation_cache = json.load(f)
        except Exception as e:
            print(f"Error loading elevation cache: {str(e)}")
            _elevation_cache = {}
    else:
        _elevation_cache = {}

# Save cache to disk
def save_elevation_cache():
    """Save the elevation cache to disk"""
    # Limit cache size to prevent excessive file sizes
    print(f"Currently cached:  {len(_elevation_cache)}")
    if len(_elevation_cache) > cacheSize:
        # Keep only the most recent entries
        keys = list(_elevation_cache.keys())
        for key in keys[:-cacheSize]:
            del _elevation_cache[key]
            
    try:
        with open(elevation_cache_file, "w") as f:
            json.dump(_elevation_cache, f)
    except Exception as e:
        print(f"Error saving elevation cache: {str(e)}")

def get_cached_elevation(lat, lon, api_type="opentopodata"):
    """Get elevation from cache if available"""
    key = f"{lat:.5f}_{lon:.5f}_{api_type}"
    return _elevation_cache.get(key)

def cache_elevation(lat, lon, elevation, api_type="opentopodata"):
    """Cache elevation data"""
    key = f"{lat:.5f}_{lon:.5f}_{api_type}"
    _elevation_cache[key] = elevation

def setupColors():
    #Create or get green material
    mat_name = "BASE"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.05, 0.7, 0.05, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------
    #Create or get green material
    mat_name = "FOREST"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.05, 0.25, 0.05, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Gray material
    mat_name = "MOUNTAIN"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.5, 0.5, 0.5, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Blue material
    mat_name = "WATER"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.0, 0.0, 0.8, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Red material
    mat_name = "TRAIL"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (1.0, 0.0, 0.0, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Yellow material
    mat_name = "CITY"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.7, 0.7, 0.1, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    #Create or get Whiteish material
    mat_name = "GLACIER"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.8, 0.9, 0.8, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------


    
    #Create or get Black material
    mat_name = "BLACK"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.0, 0.0, 0.0, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------
    

    
    #Create or get White material
    mat_name = "WHITE"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (1.0, 1.0, 1.0, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------



def calculate_scale(mapSize, coordinates, tp):
    
    
    #for lat, lon, ele in coordinates:
    min_lat = min(point[0] for point in coordinates)
    max_lat = max(point[0] for point in coordinates)
    min_lon = min(point[1] for point in coordinates)
    max_lon = max(point[1] for point in coordinates)

    print(f"min_lon: {min_lon}")
    
    R = 6371  # Earth's radius in meters (Web Mercator standard)
    #x1 = R * math.radians(min_lon)
    #x1 = R * math.radians(min_lon) * math.cos(math.radians(min_lat))
    #y1 = R * math.log(math.tan(math.pi / 4 + math.radians(min_lat) / 2))
    #x2 = R * math.radians(max_lon)
    #x2 = R * math.radians(max_lon) * math.cos(math.radians(max_lat))
    #y2 = R * math.log(math.tan(math.pi / 4 + math.radians(max_lat) / 2))
    #width = abs(x2 - x1)
    #height = abs(y2 - y1)
    #distance = math.sqrt((x2 - x1)**2 + (y2 - y1)**2)

    print(f"min_lat: {min_lat}, min_lon: {min_lon}")
    x1, y1, e = convert_to_neutral_coordinates(min_lat, min_lon, 0,0)
    x2, y2, e = convert_to_neutral_coordinates(max_lat, max_lon, 0,0)

    if scalemode == "FACTOR" and tp != 2:
        width = abs(x2 - x1)
        height = abs(y2 - y1)
        distance = math.sqrt((x2 - x1)**2 + (y2 - y1)**2)

    else:
        width = haversine(min_lat, min_lon, min_lat, max_lon) * 1
        height = haversine(min_lat, min_lon, max_lat,min_lon) * 1
        distance = haversine(min_lat,min_lon,max_lat,max_lon)*1



    print(f"Distance in km: {width}")
    print(f"Distance in km: {height}")
    print(f"Distance in km: {distance}")

    #COMMENTED OUT
    #CALCULATES THE ACCURATE SCALE BUT MULTIPLE PATHS TO EACH OTHER WONT ALIGN CORRECTLY WITH IT AS THE "mf"
    #IS DIFFRENT FOR EACH LATITUDE AND THEREFORE HAS A DIFFRENT "COORDINATE SYSTEM"
    if scalemode == "SCALE":
        mx1 = x1 = R * math.radians(min_lon) * math.cos(math.radians(min_lat))
        mx2 = x2 = R * math.radians(max_lon) * math.cos(math.radians(max_lat))
        mwidth = abs(mx1 - mx2)
        mf = 1/width * mwidth
        mf = 1
        print(f"mf: {mf}")

    if scalemode == "COORDINATES" or scalemode == "SCALE":
        distance = 0

    print(f"width: {width}")
    print(f"height: {height}")

    maxer = max(width,height, distance)

    print(f"maxer:{maxer}")
    scale = 1
    print(f"Scalemode: {scalemode}")
    print(f"tp: {tp}")
    if scalemode == "COORDINATES" or tp == 2 or tp == 3:
        print("scalemode1")
        scale = mapSize / maxer
    elif scalemode == "FACTOR":
        scale = (mapSize * pathScale) / maxer
        print(scale)
        print("scalemode2")
    elif scalemode == "SCALE":
        scale = pathScale * mf
        print("scalemode3")

    return scale

def convert_to_blender_coordinates(lat, lon, elevation,timestamp):

    scaleHor = bpy.context.scene.tp3d.sScaleHor

    
    R = 6371  # Earth's radius in meters (Web Mercator standard)
    x = R * math.radians(lon) * scaleHor
    y = R * math.log(math.tan(math.pi / 4 + math.radians(lat) / 2)) * scaleHor
    z = (elevation - elevationOffset) /1000 * scaleElevation * autoScale

    
    return (x, y, z)

def convert_to_neutral_coordinates(lat, lon, elevation,timestamp):


    
    R = 6371  # Earth's radius in meters (Web Mercator standard)
    x = R * math.radians(lon)
    y = R * math.log(math.tan(math.pi / 4 + math.radians(lat) / 2))
    z = (elevation - elevationOffset) /1000 * scaleElevation * autoScale
    
    
    
    
    return (x, y, z)


# Convert offsets to latitude/longitude
def convert_to_geo(x,y):
    """Converts Blender x/y offsets to latitude/longitude."""

    scaleHor = bpy.context.scene.tp3d.sScaleHor
    
    R = 6371  # Earth's radius in meters (Web Mercator standard)
    longitude = math.degrees((x) / (R * scaleHor) )
    latitude = math.degrees(2 * math.atan(math.exp((y) / (R * scaleHor) )) - math.pi / 2)
    return latitude, longitude

def create_curve_from_coordinates(coordinates):
    """
    Create a curve in Blender based on a list of (x, y, z) coordinates.
    """
    # Create a new curve object
    curve_data = bpy.data.curves.new('GPX_Curve', type='CURVE')
    curve_data.dimensions = '3D'
    polyline = curve_data.splines.new('POLY')
    polyline.points.add(count=len(coordinates) - 1)

    # Populate the curve with points
    for i, coord in enumerate(coordinates):
        polyline.points[i].co = (coord[0], coord[1], coord[2], 1)  # (x, y, z, w)

    # Create an object with this curve
    curve_object = bpy.data.objects.new('GPX_Curve_Object', curve_data)
    bpy.context.collection.objects.link(curve_object)
    curve_object.data.bevel_depth = pathThickness/2  # Set the thickness of the curve
    curve_object.data.bevel_resolution = 4  # Set the resolution for smoothness
    
    curve_object.data.use_fill_caps = True
    props = bpy.context.scene.tp3d

    if props.pathRemeshEnabled:
        mod = curve_object.modifiers.new(name="Remesh",type="REMESH")
        mod.mode = "VOXEL"
        min_voxel = max(0.01, pathThickness / 24)
        mod.voxel_size = max(min_voxel, pathThickness / 8)
        mod.adaptivity = 0.0

        depsgraph = bpy.context.evaluated_depsgraph_get()
        eval_obj = curve_object.evaluated_get(depsgraph)
        eval_mesh = eval_obj.to_mesh()
        is_manifold = True
        if eval_mesh is not None:
            bm = bmesh.new()
            bm.from_mesh(eval_mesh)
            is_manifold = all(edge.is_manifold for edge in bm.edges)
            bm.free()
            eval_obj.to_mesh_clear()

        if not curve_object.data.use_fill_caps:
            curve_object.data.use_fill_caps = True

        if not is_manifold:
            mod.voxel_size = max(min_voxel, mod.voxel_size * 0.75)
            eval_obj = curve_object.evaluated_get(depsgraph)
            eval_mesh = eval_obj.to_mesh()
            if eval_mesh is not None:
                bm = bmesh.new()
                bm.from_mesh(eval_mesh)
                is_manifold = all(edge.is_manifold for edge in bm.edges)
                bm.free()
                eval_obj.to_mesh_clear()
            if not is_manifold:
                curve_object.modifiers.remove(mod)
        
    curve_object.data.name = name + "_Trail"
    curve_object.name = name + "_Trail"
    
    
    curve_object.select_set(True)


    bpy.context.view_layer.objects.active = curve_object

    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.curve.select_all(action='SELECT')
    #bpy.ops.curve.smooth()
    bpy.ops.object.mode_set(mode='OBJECT')



    # Convert to mesh
    if shape == "HEXAGON INNER TEXT" or shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
        #bpy.ops.object.convert(target='MESH')
        pass

def densify_path_segments(points, max_len):
    """Insert evenly spaced intermediate points for segments longer than max_len."""
    if len(points) < 2 or max_len <= 0:
        return points

    densified = [points[0]]

    for start, end in zip(points, points[1:]):
        start_vec = Vector(start[:3])
        end_vec = Vector(end[:3])
        segment = end_vec - start_vec
        segment_length = segment.length

        if segment_length > max_len:
            inserts = int(math.ceil(segment_length / max_len)) - 1
            for i in range(1, inserts + 1):
                t = i / (inserts + 1)
                interp = start_vec.lerp(end_vec, t)
                densified.append((interp.x, interp.y, interp.z))

        densified.append(end)

    return densified


def resample_path_spacing(points, target_spacing):
    """Resample a polyline to near-uniform point spacing."""
    if len(points) < 2 or target_spacing <= 0:
        return points

    vec_points = [Vector(pt[:3]) for pt in points]
    cumulative = [0.0]
    for a, b in zip(vec_points, vec_points[1:]):
        cumulative.append(cumulative[-1] + (b - a).length)

    total_length = cumulative[-1]
    if total_length <= target_spacing:
        return [points[0], points[-1]]

    sample_count = max(2, int(round(total_length / target_spacing)) + 1)
    step = total_length / (sample_count - 1)

    out = []
    seg_idx = 0
    for i in range(sample_count):
        dist = min(i * step, total_length)
        while seg_idx < len(cumulative) - 2 and cumulative[seg_idx + 1] < dist:
            seg_idx += 1

        start_d = cumulative[seg_idx]
        end_d = cumulative[seg_idx + 1]
        start_v = vec_points[seg_idx]
        end_v = vec_points[seg_idx + 1]
        if end_d == start_d:
            interp = start_v
        else:
            t = (dist - start_d) / (end_d - start_d)
            interp = start_v.lerp(end_v, t)

        out.append((interp.x, interp.y, interp.z))

    return out

def simplify_curve(points_with_extra, min_distance=0.1000):
    """
    Removes points that are too close to any previously accepted point.
    Keeps the full (x, y, z, time) format.
    """

    if not points_with_extra:
        return []

    simplified = [points_with_extra[0]]
    last_xyz = Vector(points_with_extra[0][:3])
    skipped = 0

    for pt in points_with_extra[1:]:
        current_xyz = Vector(pt[:3])
        if (current_xyz - last_xyz).length >= min_distance:
            simplified.append(pt)
            last_xyz = current_xyz
        else:
            skipped += 1
            pass

    print(f"Smooth curve: Removed {skipped} vertices")
    return simplified

@log_workflow
def create_hexagon(size):
    """Creates a hexagon at (0,0,0), subdivides it, and rotates it by 90 degrees."""
    verts = []
    faces = []
    num_subdivisions = bpy.context.scene.tp3d.num_subdivisions

    for i in range(6):
        angle = math.radians(60 * i)
        x = size * math.cos(angle)
        y = size * math.sin(angle)
        verts.append((x, y, 0))
    verts.append((0, 0, 0))  # Center vertex
    faces = [[i, (i + 1) % 6, 6] for i in range(6)]
    mesh = bpy.data.meshes.new("Hexagon")
    obj = bpy.data.objects.new("Hexagon", mesh)
    bpy.context.collection.objects.link(obj)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    bpy.context.view_layer.objects.active = obj
    bpy.ops.object.mode_set(mode='EDIT')
    #bpy.ops.mesh.subdivide(number_cuts=num_subdivisions)
    for _ in range(num_subdivisions):
        bpy.ops.mesh.subdivide(number_cuts=1)  # 1 cut per loop for even refinement
    bpy.ops.object.mode_set(mode='OBJECT')
    obj.name = name
    obj.data.name = name
    return obj

@log_workflow
def create_rectangle(width, height):
    """Creates a rectangle at (0,0,0), subdivides it, and rotates it by 90 degrees."""

    num_subdivisions = bpy.context.scene.tp3d.get('num_subdivisions', 4)
    verts = [
        (-width / 2, -height / 2, 0),  # Bottom-left
        (width / 2, -height / 2, 0),   # Bottom-right
        (width / 2, height / 2, 0),    # Top-right
        (-width / 2, height / 2, 0)    # Top-left
    ]
    faces = [[0, 1, 2, 3]]
    mesh = bpy.data.meshes.new("Rectangle")
    obj = bpy.data.objects.new("Rectangle", mesh)
    bpy.context.collection.objects.link(obj)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    bpy.context.view_layer.objects.active = obj
    bpy.ops.object.mode_set(mode='EDIT')
    for _ in range(num_subdivisions+1):
        bpy.ops.mesh.subdivide(number_cuts=1)  # 1 cut per loop for even refinement
    #bpy.ops.mesh.subdivide(number_cuts=num_subdivisions)  # Can change number of subdivisions if needed
    bpy.ops.object.mode_set(mode='OBJECT')
    obj.name = name
    obj.data.name = name
    
    return obj









# Get real elevation for a point
def get_elevation_single(lat, lon):
    """Fetches real elevation for a single latitude and longitude using OpenTopoData."""
    url = f"https://api.opentopodata.org/v1/{dataset}?locations={lat},{lon}"
    response = requests.get(url).json()
    elevation = response['results'][0]['elevation'] if 'results' in response else 0
    return elevation  # Scale down elevation to match Blender terrain


def get_elevation_openTopoData(coords, lenv = 0, pointsDone = 0):
    """Fetches real elevation for each vertex using OpenTopoData with request batching."""

    disableCache = bpy.context.scene.tp3d.get("disableCache",0)

    # Ensure the cache is loaded
    if not _elevation_cache:
        load_elevation_cache()

    # First, check which coordinates need fetching (not in cache)
    coords_to_fetch = []
    coords_indices = []

    elevations = [0] * len(coords)  # Pre-allocate list


    
    #check if coordinates are in cache or not
    for i, (lat, lon) in enumerate(coords):
        cached_elevation = get_cached_elevation(lat, lon)
        if cached_elevation is not None and disableCache == 0:
            # Use cached elevation
            elevations[i] = cached_elevation
        else:
            # Need to fetch this coordinate
            elevations[i] = -5
            coords_to_fetch.append((lat, lon))
            coords_indices.append(i)

    if len(coords) - len(coords_to_fetch) > 0:
        print(f"Using: {len(coords) - len(coords_to_fetch)} cached Coordinates")
    
    # If all elevations were found in cache, return immediately
    if not coords_to_fetch:
        return elevations
    
    #coords = [convert_to_geo(y, x, v[0], v[1]) for v in vertices]
    #elevations = []
    batch_size = 100
    for i in range(0, len(coords_to_fetch), batch_size):
        batch = coords_to_fetch[i:i + batch_size]
        query = "|".join([f"{c[0]},{c[1]}" for c in batch])
        url = f"{opentopoAdress}{dataset}?locations={query}"
        #print(url)
        last_request_time = time.monotonic()
        response = requests.get(url)
        nr = i + len(batch) + pointsDone
        addition = f" {nr}/{int(lenv)}"
        send_api_request(addition)
        response.raise_for_status()
        
        
        data = response.json()
        # Handle the elevation data and replace 'null' with 0
        for o, result in enumerate(data['results']):
            elevation = result.get('elevation', None)  # Safe get, default to None if key is missing
            if elevation is None:
                elevation = 0  # Replace None (null in JSON) with 0
            cache_elevation(batch[o][0], batch[o][1], elevation)
            ind = coords_indices[i+o]
            elevations[ind] = elevation
        
        # Get current time
        now = time.monotonic()  # Monotonic time is safer for measuring elapsed time
        elapsed_time = now - last_request_time
        if i + batch_size < len(coords_to_fetch) and elapsed_time < 1.3:
            time.sleep(1.3 - elapsed_time)  # Pause to prevent request throttling



    return elevations



def get_elevation_usgs_tnm(coords, lenv=0, pointsDone=0):
    """Fetches real elevation for each vertex using USGS TNM 3DEP exportImage raster query."""
    if rasterio is None:
        print("USGS TNM 3DEP unavailable: rasterio is not installed")
        return [0] * len(coords)
    if not coords:
        return []

    disableCache = bpy.context.scene.tp3d.get("disableCache", 0)
    enable_map_cache = bpy.context.scene.tp3d.get("enableMapCache", True)

    # Ensure the cache is loaded
    if not _elevation_cache:
        load_elevation_cache()

    elevations = [0] * len(coords)
    cache_hits = 0
    cache_zero_hits = 0
    network_calls = 0
    network_zero_results = 0
    first_network_url = None

    module_logger.info(
        "USGS TNM start | total_points=%s | disableCache=%s | enableMapCache=%s | cache_entries=%s | pointsDone=%s | lenv=%s",
        len(coords),
        disableCache,
        enable_map_cache,
        len(_elevation_cache),
        pointsDone,
        lenv,
    )

    coords_to_fetch = []
    coords_indices = []
    for i, (lat, lon) in enumerate(coords):
        cached_elevation = get_cached_elevation(lat, lon, api_type="usgs_tnm")
        if cached_elevation is not None and disableCache == 0:
            cache_hits += 1
            elevations[i] = cached_elevation
            if cached_elevation == 0:
                cache_zero_hits += 1
        else:
            coords_to_fetch.append((lat, lon))
            coords_indices.append(i)

    module_logger.info(
        "USGS TNM cache partition | total=%s | cache_hits=%s | cache_misses=%s | disableCache=%s",
        len(coords),
        cache_hits,
        len(coords_to_fetch),
        disableCache,
    )

    if not coords_to_fetch:
        module_logger.info("USGS TNM early return | all points served from cache")
        return elevations

    lats = [c[0] for c in coords_to_fetch]
    lons = [c[1] for c in coords_to_fetch]
    pad = 0.0002
    min_lat = min(lats) - pad
    max_lat = max(lats) + pad
    min_lon = min(lons) - pad
    max_lon = max(lons) + pad
    module_logger.info(
        "USGS TNM bbox computed | min_lon=%s min_lat=%s max_lon=%s max_lat=%s | pad=%s",
        min_lon,
        min_lat,
        max_lon,
        max_lat,
        pad,
    )

    cache_key = hashlib.sha1(
        f"{min_lon},{min_lat},{max_lon},{max_lat}|1024x1024|4326|tiff|F32".encode("utf-8")
    ).hexdigest()
    raster_path = os.path.join(tnm_3dep_cache_dir, f"{cache_key}.tif")
    raster_exists = os.path.exists(raster_path)
    should_download = (not enable_map_cache) or (not raster_exists)
    module_logger.info(
        "USGS TNM raster cache target | key=%s | path=%s | exists=%s | enableMapCache=%s | should_download=%s",
        cache_key,
        raster_path,
        raster_exists,
        enable_map_cache,
        should_download,
    )

    if should_download:
        metadata_params = {
            "bbox": f"{min_lon},{min_lat},{max_lon},{max_lat}",
            "bboxSR": 4326,
            "imageSR": 4326,
            "size": "1024,1024",
            "format": "tiff",
            "pixelType": "F32",
            "f": "json",
        }
        metadata_url = "https://elevation.nationalmap.gov/arcgis/rest/services/3DEPElevation/ImageServer/exportImage?" + urlencode(metadata_params)
        network_calls += 1
        module_logger.info("USGS TNM metadata request | url=%s", metadata_url)
        req = Request(metadata_url, headers=get_usgs_auth_headers())
        with urlopen(req, timeout=20) as resp:
            module_logger.info("USGS TNM metadata response | status=%s", getattr(resp, "status", None))
            metadata = json.loads(resp.read().decode("utf-8", "replace"))
        module_logger.info("USGS TNM metadata payload | keys=%s", list(metadata.keys()))
        href = metadata.get("href")
        if not href:
            raise ValueError(f"USGS TNM 3DEP metadata missing href: {metadata}")
        module_logger.info("USGS TNM raster href | href=%s", href)
        if first_network_url is None:
            first_network_url = metadata_url
        req = Request(href, headers=get_usgs_auth_headers())
        with urlopen(req, timeout=25) as resp:
            module_logger.info(
                "USGS TNM raster download response | status=%s | content_type=%s",
                getattr(resp, "status", None),
                resp.headers.get("Content-Type"),
            )
            raster_bytes = resp.read()
        module_logger.info("USGS TNM raster download bytes | size=%s", len(raster_bytes))
        if enable_map_cache:
            with open(raster_path, "wb") as f_raster:
                f_raster.write(raster_bytes)
            module_logger.info("USGS TNM raster saved | path=%s", raster_path)
        else:
            with open(raster_path, "wb") as f_raster:
                f_raster.write(raster_bytes)
            module_logger.info("USGS TNM map cache disabled | downloaded raster written for immediate sampling only | path=%s", raster_path)
    else:
        module_logger.info("USGS TNM raster cache hit | path=%s", raster_path)

    with rasterio.open(raster_path) as src:
        module_logger.info(
            "USGS TNM raster opened | crs=%s | bounds=%s | width=%s | height=%s | nodata=%s | dtypes=%s",
            src.crs,
            src.bounds,
            src.width,
            src.height,
            src.nodata,
            src.dtypes,
        )
        try:
            band = src.read(1, masked=True)
            band_min = float(band.min()) if band.size else None
            band_max = float(band.max()) if band.size else None
            module_logger.info(
                "USGS TNM raster band stats | min=%s | max=%s | masked=%s",
                band_min,
                band_max,
                int(getattr(band, "mask", []).sum()) if hasattr(band, "mask") else "n/a",
            )
        except Exception:
            module_logger.exception("USGS TNM raster band stats failed")

        sampled_values = []
        for pos, (lat, lon) in enumerate(coords_to_fetch):
            nr = pos + 1 + pointsDone
            addition = f" {nr}/{int(lenv)}"
            send_api_request(addition)
            try:
                sample = next(src.sample([(lon, lat)]))[0]
                if sample is None:
                    elevation = 0
                    network_zero_results += 1
                else:
                    elevation = float(sample)
                    sampled_values.append(elevation)
            except Exception:
                elevation = 0
                network_zero_results += 1
            cache_elevation(lat, lon, elevation, api_type="usgs_tnm")
            elevations[coords_indices[pos]] = elevation
            if pos < 5:
                module_logger.info(
                    "USGS TNM sample point | idx=%s | lat=%s lon=%s | elevation=%s",
                    pos,
                    lat,
                    lon,
                    elevation,
                )

        if sampled_values:
            module_logger.info(
                "USGS TNM sampled stats | count=%s | min=%s | max=%s | avg=%s",
                len(sampled_values),
                min(sampled_values),
                max(sampled_values),
                sum(sampled_values) / len(sampled_values),
            )
        else:
            module_logger.warning("USGS TNM sampled stats | no non-null sample values collected")

    sample_coords = coords[:3]
    sample_elevations = elevations[:3]
    module_logger.info(
        "USGS TNM summary | points=%s | cache_hits=%s | cache_zero_hits=%s | network_calls=%s | network_zero_results=%s | disableCache=%s | first_network_url=%s | sample_coords=%s | sample_elevations=%s",
        len(coords),
        cache_hits,
        cache_zero_hits,
        network_calls,
        network_zero_results,
        disableCache,
        first_network_url,
        sample_coords,
        sample_elevations,
    )
    return elevations

def get_elevation_openElevation(coords, lenv = 0, pointsDone = 0):
    """Fetches real elevation for each vertex using Open-Elevation with request batching."""
    
    elevations = []
    batch_size = 1000
    for i in range(0, len(coords), batch_size):
        batch = coords[i:i + batch_size]
        # Open-Elevation expects a POST request with JSON body
        payload = {"locations": [{"latitude": c[0], "longitude": c[1]} for c in batch]}
        url = "https://api.open-elevation.com/api/v1/lookup"
        last_request_time = time.monotonic()
        
        headers = {'Content-Type': 'application/json'}
        nr = i + len(batch) + pointsDone
        addition = f" {nr}/{int(lenv)}"
        send_api_request(addition)
        
        response = requests.post(url, json=payload, headers=headers)
        
        #print(url)
        #print(payload)
        
        response.raise_for_status()

        data = response.json()
        
        
        # Handle the elevation data and replace 'null' with 0
        for result in data['results']:
            elevation = result.get('elevation', None)
            if elevation is None:
                elevation = 0
            elevations.append(elevation)
        
        # Get current time for request rate limiting
        now = time.monotonic()  
        elapsed_time = now - last_request_time
        if elapsed_time < 2:
            time.sleep(2 - elapsed_time)  # Pause to prevent request throttling

    return elevations

def lonlat_to_tilexy(lon, lat, zoom):
    lat_rad = math.radians(lat)
    n = 2.0 ** zoom
    xtile = int((lon + 180.0) / 360.0 * n)
    ytile = int((1.0 - math.log(math.tan(lat_rad) + 1.0 / math.cos(lat_rad)) / math.pi) / 2.0 * n)
    return xtile, ytile

def lonlat_to_pixelxy(lon, lat, zoom):
    lat_rad = math.radians(lat)
    n = 2.0 ** zoom
    x = (lon + 180.0) / 360.0 * n * 256
    y = (1.0 - math.log(math.tan(lat_rad) + 1.0 / math.cos(lat_rad)) / math.pi) / 2.0 * n * 256
    return int(x % 256), int(y % 256)

def fetch_terrarium_tile_raw(zoom, xtile, ytile):
    """Fetch the raw PNG binary data for a tile, either from cache or online."""
    tile_path = os.path.join(terrarium_cache_dir, f"{zoom}_{xtile}_{ytile}.png")
    if not os.path.exists(tile_path):
        url = f"https://elevation-tiles-prod.s3.amazonaws.com/terrarium/{zoom}/{xtile}/{ytile}.png"
        #print("Sending Request")
        response = requests.get(url)
        response.raise_for_status()
        with open(tile_path, "wb") as f:
            f.write(response.content)
    with open(tile_path, "rb") as f:
        return f.read()

def paeth_predictor(a, b, c):
    # PNG Paeth filter
    p = a + b - c
    pa = abs(p - a)
    pb = abs(p - b)
    pc = abs(p - c)
    if pa <= pb and pa <= pc:
        return a
    elif pb <= pc:
        return b
    else:
        return c

def parse_png_rgb_data(png_bytes):
    """Extract uncompressed RGB bytes from a PNG image (supports all PNG filter types)."""
    assert png_bytes[:8] == b'\x89PNG\r\n\x1a\n', "Not a valid PNG file"
    offset = 8
    width = height = None
    idat_data = b''

    while offset < len(png_bytes):
        length = struct.unpack(">I", png_bytes[offset:offset+4])[0]
        chunk_type = png_bytes[offset+4:offset+8]
        data = png_bytes[offset+8:offset+8+length]
        offset += 12 + length

        if chunk_type == b'IHDR':
            width, height, bit_depth, color_type, _, _, _ = struct.unpack(">IIBBBBB", data)
            assert bit_depth == 8 and color_type == 2, "Only 8-bit RGB PNGs supported"
        elif chunk_type == b'IDAT':
            idat_data += data
        elif chunk_type == b'IEND':
            break

    raw = zlib.decompress(idat_data)
    stride = 3 * width
    rgb_array = []
    prev_row = bytearray(stride)

    for y in range(height):
        i = y * (stride + 1)
        filter_type = raw[i]
        scanline = bytearray(raw[i + 1:i + 1 + stride])
        recon = bytearray(stride)

        if filter_type == 0:
            recon[:] = scanline
        elif filter_type == 1:  # Sub
            for i in range(stride):
                val = scanline[i]
                left = recon[i - 3] if i >= 3 else 0
                recon[i] = (val + left) % 256
        elif filter_type == 2:  # Up
            for i in range(stride):
                recon[i] = (scanline[i] + prev_row[i]) % 256
        elif filter_type == 3:  # Average
            for i in range(stride):
                left = recon[i - 3] if i >= 3 else 0
                up = prev_row[i]
                recon[i] = (scanline[i] + (left + up) // 2) % 256
        elif filter_type == 4:  # Paeth
            for i in range(stride):
                a = recon[i - 3] if i >= 3 else 0
                b = prev_row[i]
                c = prev_row[i - 3] if i >= 3 else 0
                recon[i] = (scanline[i] + paeth_predictor(a, b, c)) % 256
        else:
            raise ValueError(f"Unsupported filter type {filter_type}")

        # Convert scanline to list of (R, G, B) tuples
        row = [(recon[i], recon[i+1], recon[i+2]) for i in range(0, stride, 3)]
        rgb_array.append(row)
        prev_row = recon

    return rgb_array


def terrarium_pixel_to_elevation(r, g, b):
    """Convert Terrarium RGB pixel to elevation in meters."""
    return (r * 256 + g + b / 256) - 32768

def get_elevation_TerrainTiles(coords, lenv=0, pointsDone=0, zoom=10):

    #Each Tile requested is a PNG that is 256x256 Pixels big

    realdist1 = haversine(minLat,minLon,minLat,maxLon)*1000
    realdist2 = haversine(maxLat,minLon,maxLat,maxLon)*1000

    #calculating zoom
    zoom = 10
    horVerts = 1 + 2**(num_subdivisions+1)
    dist = 25.00000 / 2**(num_subdivisions-1) #25 is the rough distance between verts on resolution 1
    strt = 156543 #m/Pixel on Tile PNG
    #print(f"dist:{dist}")
    cntr = 2

    #print(f"scaleHor: {scaleHor}")
    vertdist = max(realdist1,realdist2)/horVerts #Distance between 2 vertices
    while strt > vertdist:
        cntr += 1
        strt /= 2
        #print(f"halved: {strt:.2f}, {cntr}, {vertdist:.2f}")
    #Max zoom level to 14
    cntr = min(cntr,15)

    #print(f"horVerts: {horVerts}")
    print(f"Zoom Level for API: {cntr}, Start fetching Data...")
        #print(f"calculated distance: {dist}")
    zoom = cntr
    
    
    


    tile_dict = {}
    for idx, (lat, lon) in enumerate(coords):
        xtile, ytile = lonlat_to_tilexy(lon, lat, zoom)
        tile_dict.setdefault((xtile, ytile), []).append((idx, lat, lon))

    total_tiles = len(tile_dict)
    progress_intervals = set(range(10,101,10))
    elevations = [0] * len(coords)
    for i, ((xtile, ytile), idx_lat_lon_list) in enumerate(tile_dict.items(), 1):
        percent_complete = int((i/ total_tiles) * 100)
        if percent_complete in progress_intervals:
            print(f"{datetime.now().strftime('%H:%M:%S')} - {percent_complete}% complete, {i}")
            progress_intervals.remove(percent_complete)
        try:
            png_bytes = fetch_terrarium_tile_raw(zoom, xtile, ytile)
            rgb_array = parse_png_rgb_data(png_bytes)
        except Exception as e:
            print(f"Failed to fetch or parse tile {zoom}/{xtile}/{ytile}: {e}")
            for idx, _, _ in idx_lat_lon_list:
                elevations[idx] = 0
            continue

        for idx, lat, lon in idx_lat_lon_list:
            px, py = lonlat_to_pixelxy(lon, lat, zoom)
            px = min(max(px, 0), 255)
            py = min(max(py, 0), 255)
            r, g, b = rgb_array[py][px]
            temp_ele = terrarium_pixel_to_elevation(r, g, b)
            if temp_ele < -1:
                temp_ele = -1
                global buggyDataset
                buggyDataset = 1
            elevations[idx] = temp_ele

            

    return elevations

def get_elevation_path_openElevation(vertices):
    """Fetches real elevation for each vertex using OpenTopoData with request batching."""
    v = vertices
    coords = [(v[0], v[1], v[2], v[3]) for v in vertices]
    elevations = []
    batch_size = 1000
    for i in range(0, len(coords), batch_size):
        batch = coords[i:i + batch_size]
        # Open-Elevation expects a POST request with JSON body
        payload = {"locations": [{"latitude": c[0], "longitude": c[1]} for c in batch]}
        url = "https://api.open-elevation.com/api/v1/lookup"
        last_request_time = time.monotonic()
        
        headers = {'Content-Type': 'application/json'}

        addition = f"(overwrite path) {i + len(batch)}/{len(coords)}"
        send_api_request(addition)

        response = requests.post(url, json=payload, headers=headers)
        
        #print(url)
        #print(payload)
        
        response.raise_for_status()

        data = response.json()
        
        elevations.extend([r['elevation'] for r in data['results']])
        now = time.monotonic()  # Monotonic time is safer for measuring elapsed time
        elapsed_time = now - last_request_time
        if i + batch_size < len(coords) and elapsed_time < 1.4:
            time.sleep(1.4 - elapsed_time)  # Pause to prevent request throttling
    
    for i in range(len(vertices)):
        coords[i] =  (coords[i][0], coords[i][1], elevations[i], coords[i][3])
        #print(elevations[i])
    
    return coords
# Get real elevation for each vertex

def get_elevation_path_openTopoData(vertices):
    """Fetches real elevation for each vertex using OpenTopoData with request batching."""
    v = vertices
    coords = [(v[0], v[1], v[2], v[3]) for v in vertices]
    elevations = []
    batch_size = 100
    for i in range(0, len(coords), batch_size):
        batch = coords[i:i + batch_size]
        query = "|".join([f"{c[0]},{c[1]}" for c in batch])
        url = f"{opentopoAdress}{dataset}?locations={query}"
        last_request_time = time.monotonic()
        response = requests.get(url).json()
        addition = f"(overwrite path) {i + len(batch)}/{len(coords)}"
        send_api_request(addition)
        
        #elevations.extend([r['elevation'] for r in response['results']])
        elevations.extend([r.get('elevation') or 0 for r in response['results']])

        now = time.monotonic()  # Monotonic time is safer for measuring elapsed time
        elapsed_time = now - last_request_time
        if i + batch_size < len(coords) and elapsed_time < 1.4:
            time.sleep(1.4 - elapsed_time)  # Pause to prevent request throttling
    
    for i in range(len(vertices)):
        coords[i] =  (coords[i][0], coords[i][1], elevations[i], coords[i][3])
        #print(elevations[i])
    
    return coords

def RaycastCurveToMesh(curve_obj, mesh_obj):
    if mesh_obj is None or mesh_obj.type != 'MESH' or mesh_obj.data is None or len(mesh_obj.data.polygons) == 0:
        module_logger.warning("Skipping path elevation overwrite: invalid mesh target")
        return

    print("---")
    print(mesh_obj.name)
    #MOVE EVERY POINT UP BY 100 SO ITS POSSIBLE TO RAYCAST IT DOWNARDS ONTO THE MESH
    offset = Vector((0, 0, 1000))
    for spline in curve_obj.data.splines:
        if spline.type == 'BEZIER':
            for p in spline.bezier_points:
                p.co += offset
                # if you want to move the handles too:
                p.handle_left += offset
                p.handle_right += offset
        else:  # POLY / NURBS
            for p in spline.points:
                p.co = (p.co.x, p.co.y, p.co.z + offset.z, p.co.w)

    bpy.context.view_layer.update()
    depsgraph = bpy.context.evaluated_depsgraph_get()
    eval_mesh_obj = mesh_obj.evaluated_get(depsgraph)

    curve_world     = curve_obj.matrix_world
    curve_world_inv = curve_world.inverted()

    mesh_world     = eval_mesh_obj.matrix_world
    mesh_world_inv = mesh_world.inverted()

    direction_world = Vector((0, 0, -1))  # world -Z
    direction_local = (mesh_world_inv.to_3x3() @ direction_world).normalized()

    for spline in curve_obj.data.splines:
        if spline.type == 'BEZIER':
            points = spline.bezier_points
        else:
            points = spline.points

        for point in points:
            # world-space position of curve point
            if spline.type == 'BEZIER':
                co_world = curve_world @ point.co
            else:
                co_world = curve_world @ point.co.xyz

            # convert origin to mesh local
            co_local = mesh_world_inv @ co_world

            # raycast in mesh local space
            success, hit_loc, normal, face_index = eval_mesh_obj.ray_cast(co_local, direction_local)

            if success:
                # back to world space
                hit_world = mesh_world @ hit_loc
                # then into curve local
                local_hit = curve_world_inv @ hit_world

                if spline.type == 'BEZIER':
                    point.co = local_hit
                    point.handle_left_type = point.handle_right_type = 'AUTO'
                else:
                    point.co = (local_hit.x, local_hit.y, local_hit.z, 1.0)
            else:
                point.co -= Vector((offset.x, offset.y, offset.z, 1.0))
    
    bpy.context.view_layer.objects.active = curve_obj
    bpy.ops.object.mode_set(mode='EDIT')

    # select all points if you want to smooth everything
    bpy.ops.curve.select_all(action='SELECT')

    # run the smooth operator
    bpy.ops.curve.smooth()

    # back to Object Mode if you like
    bpy.ops.object.mode_set(mode='OBJECT')

    print("Path Elevation Overwritten")

def RaycastCurveToAnyMesh(curve_obj, offset_z=1000.0, smooth_after=True):
    """Move curve points up by offset_z then raycast straight down onto any mesh below.
    Uses scene.ray_cast so the nearest mesh hit is used automatically.
    """

    print("Raycasting")
    scene = bpy.context.scene
    depsgraph = bpy.context.evaluated_depsgraph_get()

    offset = Vector((0.0, 0.0, offset_z))

    # Move points up by offset so we can raycast downwards
    for spline in curve_obj.data.splines:
        if spline.type == 'BEZIER':
            for p in spline.bezier_points:
                p.co += offset
                p.handle_left += offset
                p.handle_right += offset
        else:  # POLY / NURBS
            for p in spline.points:
                # p.co is (x, y, z, w)
                p.co = (p.co.x, p.co.y, p.co.z + offset_z, p.co.w)

    curve_world     = curve_obj.matrix_world
    curve_world_inv = curve_world.inverted()

    # ray direction in world space: straight down
    direction_world = Vector((0.0, 0.0, -1.0))

    for spline in curve_obj.data.splines:
        if spline.type == 'BEZIER':
            points = spline.bezier_points
        else:
            points = spline.points

        for point in points:
            # get world-space position of the point
            if spline.type == 'BEZIER':
                co_world = curve_world @ point.co
            else:
                co_world = curve_world @ point.co.xyz

            # cast ray from this origin straight down in world-space
            # scene.ray_cast returns (result, location, normal, face_index, object, matrix)
            hit_result = scene.ray_cast(depsgraph, co_world, direction_world)
            hit_success = hit_result[0]

            if hit_success:
                hit_loc_world = hit_result[1]

                # convert hit back into curve local space
                local_hit = curve_world_inv @ hit_loc_world

                if spline.type == 'BEZIER':
                    point.co = local_hit
                    # keep handles auto to get a reasonable shape; alternatively compute
                    point.handle_left_type = point.handle_right_type = 'AUTO'
                else:
                    # preserve w component
                    w = getattr(point.co, "w", 1.0)
                    point.co = (local_hit.x, local_hit.y, local_hit.z, w)

    # optional smoothing (go into edit mode, smooth, come back)
    if smooth_after:
        bpy.context.view_layer.objects.active = curve_obj
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.curve.select_all(action='SELECT')
        bpy.ops.curve.smooth()
        bpy.ops.object.mode_set(mode='OBJECT')

    print("Curve projected onto nearest mesh below each point.")



# Get tile elevation
def normalize_elevation_api_value(props, api_raw):
    """Normalize legacy/int and string API values to current enum keys."""
    enum_order = ["OPENTOPODATA", "OPEN-ELEVATION", "USGS_TNM", "TERRAIN-TILES"]

    if isinstance(api_raw, str):
        stripped = api_raw.strip()
        if stripped in enum_order or stripped == "TERRARIUM":
            return stripped
        if stripped.isdigit():
            idx = int(stripped)
            if 0 <= idx < len(enum_order):
                return enum_order[idx]

    if isinstance(api_raw, int) and 0 <= api_raw < len(enum_order):
        return enum_order[api_raw]

    prop_value = getattr(props, "api", None) if props is not None else None
    if isinstance(prop_value, str) and prop_value in enum_order:
        return prop_value

    return "TERRAIN-TILES"


def get_tile_elevation(obj):

    mesh = obj.data
    global api
    props = getattr(getattr(bpy.context, "scene", None), "tp3d", None)
    api_raw = bpy.context.scene.tp3d.get("api", "TERRAIN-TILES")
    elevationApi = normalize_elevation_api_value(props, api_raw)
    api = elevationApi
    disable_cache = bpy.context.scene.tp3d.get("disableCache", 0)
    module_logger.info("get_tile_elevation start | map=%s | props.api=%s | idprop_api=%s | normalized_api=%s | disableCache=%s", getattr(obj, "name", "unknown"), getattr(props, "api", None), api_raw, elevationApi, disable_cache)

    # Set chunk size based on API
    if elevationApi in {"OPENTOPODATA", "OPEN-ELEVATION", "USGS_TNM"}:
        chunk_size = 100000
    elif elevationApi in {"TERRARIUM", "TERRAIN-TILES"}:
        chunk_size = 50000000
    else:
        chunk_size = 100000  # fallback

    module_logger.info("Elevation API selected=%s chunk_size=%s", elevationApi, chunk_size)

    vertices = list(mesh.vertices)
    obj_matrix = obj.matrix_world

    # Convert all vertex positions to world space
    world_verts = [obj_matrix @ v.co for v in vertices]

    # Get min/max bounds in world space
    min_x = min(v.x for v in world_verts)
    max_x = max(v.x for v in world_verts)
    min_y = min(v.y for v in world_verts)
    max_y = max(v.y for v in world_verts)

    global minLon, maxLon, minLat, maxLat

    # Use object's world location as reference origin
    origin_lat = obj_matrix.translation.y
    origin_lon = obj_matrix.translation.x

    minl = convert_to_geo(min_x, min_y)
    maxl = convert_to_geo(max_x, max_y)

    minLat = minl[0]
    maxLat = maxl[0]
    minLon = minl[1]
    maxLon = maxl[1]


    realdist1 = haversine(minLat,minLon,maxLat,maxLon)*1
    realdist2 = haversine(minLat,minLon,maxLat,maxLon)*1
    bpy.context.scene.tp3d["sMapInKm"] = max(realdist1,realdist2)

    elevations = []
    for i in range(0, len(world_verts), chunk_size):
        chunk = world_verts[i:i + chunk_size]

        coords = [convert_to_geo(v.x, v.y) for v in chunk]

        if elevationApi == "OPENTOPODATA":
            chunk_elevations = get_elevation_openTopoData(coords, len(vertices), i)
        elif elevationApi == "OPEN-ELEVATION":
            chunk_elevations = get_elevation_openElevation(coords, len(vertices), i)
        elif elevationApi == "USGS_TNM":
            chunk_elevations = get_elevation_usgs_tnm(coords, len(vertices), i)
        elif elevationApi in {"TERRARIUM", "TERRAIN-TILES"}:
            #print(f"Loading {i}/{len(vertices)}")
            chunk_elevations = get_elevation_TerrainTiles(coords, len(vertices), i)
        else:
            chunk_elevations = [0.0] * len(chunk)  # fallback

        elevations.extend(chunk_elevations)

        # Free memory after processing chunk
        del chunk_elevations

    save_elevation_cache()

    global lowestZ
    global highestZ
    lowestZ = min(elevations)
    highestZ = max(elevations)
    global additionalExtrusion
    additionalExtrusion = lowestZ
    diff = highestZ - lowestZ

    bpy.context.scene.tp3d["o_verticesMap"] = str(len(mesh.vertices))

    return elevations, diff

# Transform MapObject
def transform_MapObject(obj, newX, newY):
    obj.location.x += newX
    obj.location.y += newY

def haversine(lat1, lon1, lat2, lon2):
    """Calculates the great-circle distance between two points using the Haversine formula."""
    R = 6371.0  # Earth radius in kilometers
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    delta_phi = math.radians(lat2 - lat1)
    delta_lambda = math.radians(lon2 - lon1)

    a = math.sin(delta_phi / 2)**2 + math.cos(phi1) * math.cos(phi2) * math.sin(delta_lambda / 2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    distance = R * c  # distance in kilometers
    #print(f"Distance between 2 points: {distance}")
    return distance
    
    
def calculate_total_length(points):
    #Calculates the total path length in kilometers.
    total_distance = 0.0
    for i in range(1, len(points)):
        lon1, lat1, _, _ = points[i - 1]
        lon2, lat2, _, _ = points[i]
        total_distance += haversine(lon1, lat1, lon2, lat2)
    return total_distance

def calculate_total_elevation(points):
    #Calculates the total elevation gain in meters.
    total_elevation = 0.0
    for i in range(1, len(points)):
        _, _, elev1, _ = points[i - 1]
        _, _, elev2, _ = points[i]
        if elev2 > elev1:
            total_elevation += elev2 - elev1
    return total_elevation

def calculate_total_time(points):
    hrs = 0
    #Calculates the total time taken between the first and last points.
    if len(points) < 2:
        return 0.0
    start_time = points[0][3]
    end_time = points[-1][3]
    if start_time != None and end_time != None:
        time_diff = end_time - start_time
        hours = int(time_diff.total_seconds() / 3600)
        minutes = int((time_diff.total_seconds() / 3600 - hours) * 60)
        time_str = f"{hours}h {minutes}m"
        #print(time_str)
        hrs = time_diff.total_seconds() / 3600
    
    return hrs

def update_text_object(obj_name, new_text):
    """Updates the text of a Blender text object."""
    text_obj = bpy.data.objects.get(obj_name)
    if text_obj and text_obj.type == 'FONT':
        text_obj.data.body = new_text
        
def export_to_STL(zobj,force = "STL"):
    


    exportPath = bpy.context.scene.tp3d.get('export_path', None)
    bpy.ops.object.select_all(action='DESELECT')
    zobj.select_set(True)
    bpy.context.view_layer.objects.active = zobj

    if zobj.material_slots and force != "STL":  
        bpy.ops.wm.obj_export(filepath=exportPath + zobj.name + ".obj",
            export_selected_objects=True,
            export_triangulated_mesh=True, 
            apply_modifiers=True,
            export_materials=True,
            forward_axis="Y",
            up_axis="Z",
            )
        #show_message_box("File Exported as OBJ because it contains Materials","INFO","OBJ File Exported")
    else:
        bpy.ops.wm.stl_export(filepath=exportPath +  zobj.name + ".stl", export_selected_objects = True)
        #show_message_box("File Exported to your selected directory","INFO","File Exported")
    
    zobj.select_set(False)  # Select the object

def export_selected_to_STL(force = "STL"):

    exportPath = bpy.context.scene.tp3d.get('export_path', None)
    selected_objects = bpy.context.selected_objects
    active_obj = bpy.context.active_object

    if not selected_objects:
            show_message_box("No objects selected")
            return{'FINISHED'}

    for zobj in selected_objects:
        bpy.ops.object.select_all(action='DESELECT')
        zobj.select_set(True)
        bpy.context.view_layer.objects.active = zobj

        if (zobj.material_slots or force == "OBJ") and force != "STL":  
            bpy.ops.wm.obj_export(filepath=exportPath + zobj.name + ".obj",
                export_selected_objects=True,
                export_triangulated_mesh=True, 
                apply_modifiers=True,
                export_materials=True,
                forward_axis="Y",
                up_axis="Z",
                )
            #show_message_box("File Exported as OBJ because it contains Materials","INFO","OBJ File Exported")
            show_message_box("OBJ Exported to your selected directory","INFO","File Exported")
        else:
            bpy.ops.wm.stl_export(filepath=exportPath +  zobj.name + ".stl", export_selected_objects = True)
            show_message_box("STL Exported to your selected directory","INFO","File Exported")


    bpy.ops.object.select_all(action='DESELECT')
    for zobj in selected_objects:
        zobj.select_set(True)
    bpy.context.view_layer.objects.active = active_obj     


    active_obj = bpy.context.active_object





def zoom_camera_to_selected(obj):
    
    bpy.ops.object.select_all(action='DESELECT')
    
    obj.select_set(True)  # Select the object
    
    area = [area for area in bpy.context.screen.areas if area.type == "VIEW_3D"][0]
    region = area.regions[-1]

    with bpy.context.temp_override(area=area, region=region):
        bpy.ops.view3d.view_selected(use_all_regions=False)
        
        
def create_text(name, text, position, scale_multiplier, rotation=(0, 0, 0), extrude=20):
    txt_data = bpy.data.curves.new(name=name, type='FONT')
    txt_obj = bpy.data.objects.new(name=name, object_data=txt_data)
    bpy.context.collection.objects.link(txt_obj)
    
    global textFont

    if textFont == "":
        if platform.system() == "Windows":
            textFont = "C:/WINDOWS/FONTS/ariblk.ttf"
        elif platform.system() == "Darwin":
            textFont = "/System/Library/Fonts/Supplemental/Arial Black.ttf"
        else:
            textFont = ""

    txt_data.body = text
    txt_data.extrude = extrude
    #txt_data.font = bpy.data.fonts.load("C:/Windows/Fonts/ariblk.ttf")  # Adjust path if needed
    txt_data.font = bpy.data.fonts.load(textFont)
    txt_data.align_x = 'CENTER'
    txt_data.align_y = "CENTER"
    
    txt_obj.scale = (scale_multiplier, scale_multiplier, 1)
    txt_obj.location = position
    txt_obj.rotation_euler = rotation
    
    txt_obj.location.z -= 1
    
    return txt_obj

def HexagonInnerText():
    
    global total_elevation
    global total_length

    textSize = bpy.context.scene.tp3d.textSize
    textSize2 = bpy.context.scene.tp3d.textSizeTitle

    if textSize2 == 0:
        textSize2 = textSize
    
    
    
    dist =  (size/2 - size/2 * (1-pathScale)/2)
    
    temp_y = math.sin(math.radians(90)) * (dist  * math.cos(math.radians(30)))
    

    
    tName = create_text("t_name", "Name", (0, temp_y, 0.1),1)

    for i, (text_name, angle) in enumerate(zip(["t_length", "t_elevation", "t_duration"], [210, 270, 330])):
        angle_centered = angle + 90
        x = math.cos(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        y = math.sin(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        rot_z = math.radians(angle_centered)
        create_text(text_name, text_name.split("_")[1].capitalize(), (x, y, 0.1),1,  (0, 0, rot_z), 100)
    
    tElevation = bpy.data.objects.get("t_elevation")
    tLength = bpy.data.objects.get("t_length")
    tDuration = bpy.data.objects.get("t_duration")

    

    
    transform_MapObject(tName, centerx + xTerrainOffset, centery + yTerrainOffset)
    transform_MapObject(tElevation, centerx + xTerrainOffset, centery + yTerrainOffset)
    transform_MapObject(tLength, centerx + xTerrainOffset, centery + yTerrainOffset)
    transform_MapObject(tDuration,centerx + xTerrainOffset, centery + yTerrainOffset)
    

    update_text_object("t_name", f"{name}")
    update_text_object("t_elevation", f"{total_elevation:.2f} hm")
    update_text_object("t_length", f"{total_length:.2f} km")
    update_text_object("t_duration", f"{time_str}")

    if overwriteLength != "":
        update_text_object("t_length", overwriteLength)
    if overwriteHeight != "":
        update_text_object("t_elevation", overwriteHeight)
    if overwriteTime != "":
        update_text_object("t_duration", overwriteTime)
    
    #Scale text sizes to mm values (blender units)
    bpy.context.view_layer.update()
    current_height = tName.dimensions.y
    if current_height == 0:
        current_height = tElevation.dimensions.y
    if current_height == 0:
        current_height = tLength.dimensions.y
    if current_height == 0:
        current_height = 5
    scale_factor = textSize2 / current_height
    tName.scale.x *= scale_factor
    tName.scale.y *= scale_factor

    scale_factor = textSize / current_height
    tElevation.scale.x *= scale_factor
    tLength.scale.x *= scale_factor
    tDuration.scale.x *= scale_factor
    tElevation.scale.y *= scale_factor
    tLength.scale.y *= scale_factor
    tDuration.scale.y *= scale_factor

    #SHAPE ROTATION
    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    bpy.context.view_layer.objects.active = tName
    #bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')
    tName.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    tElevation.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    tLength.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    tDuration.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    
    convert_text_to_mesh("t_name", MapObject.name)
    convert_text_to_mesh("t_elevation", MapObject.name)
    convert_text_to_mesh("t_length", MapObject.name)
    convert_text_to_mesh("t_duration", MapObject.name)
    
    
    bpy.ops.object.select_all(action='DESELECT')

    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    #curveObj.select_set(True)
    
    bpy.context.view_layer.objects.active = tName
    
    bpy.ops.object.join()

    tName.name = name + "_Text"


    #SHAPE ROTATION
    tName.select_set(True)
    bpy.context.view_layer.objects.active = tName
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')


    global textobj
    textobj = tName
    
def HexagonOuterText():


    
    outersize = size * ( 1 + outerBorderSize/100)
    thickness = plateThickness
    textSize = bpy.context.scene.tp3d.textSize
    textSize2 = bpy.context.scene.tp3d.textSizeTitle

    if textSize2 == 0:
        textSize2 = textSize
    
    
    verts = []
    faces = []
    for i in range(6):
        angle = math.radians(60 * i)
        x = outersize/2 * math.cos(angle)
        y = outersize/2 * math.sin(angle)
        verts.append((x, y, 0))
    verts.append((0, 0, 0))  # Center vertex
    faces = [[i, (i + 1) % 6, 6] for i in range(6)]
    mesh = bpy.data.meshes.new("HexagonOuter")
    outerHex = bpy.data.objects.new("HexagonOuter", mesh)
    bpy.context.collection.objects.link(outerHex)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    outerHex.name = name
    outerHex.data.name = name
    
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, -8))#bpy.ops.mesh.select_all(action='DESELECT')

    bpy.ops.object.mode_set(mode='OBJECT')

    # Get the mesh data
    mesh = outerHex.data

    # Get selected faces
    selected_faces = [face for face in mesh.polygons if face.select]
    
    if selected_faces:
        for face in selected_faces:
            for vert_idx in face.vertices:
                vert = mesh.vertices[vert_idx]
                vert.co.z =  - thickness
    else:
        print("No face selected.")
    
    transform_MapObject(outerHex, centerx, centery)
    
    
    dist = (outersize - size)/4 + size/2
    
    temp_y = math.sin(math.radians(90)) * (dist  * math.cos(math.radians(30)))
    
    
    #t_name = create_text("t_name", "Name", (0, temp_y, 1 + additionalExtrusion - 2 ),text_size,(0, 0, 0),0.4)

    for i, (text_name, angle) in enumerate(zip(["t_name","t_length", "t_elevation", "t_duration"], [90 + text_angle_preset, 210 + text_angle_preset, 270 + text_angle_preset, 330 + text_angle_preset])):
        angle_centered = angle + 90
        x = math.cos(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        y = math.sin(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        rot_z = math.radians(angle_centered)
        if i == 0:
            rot_z += math.radians(180)
        create_text(text_name, text_name.split("_")[1].capitalize(), (x, y,1.4),1,  (0, 0, rot_z), 0.4)
    
    tName = bpy.data.objects.get("t_name")
    tElevation = bpy.data.objects.get("t_elevation")
    tLength = bpy.data.objects.get("t_length")
    tDuration = bpy.data.objects.get("t_duration")

    
    
    transform_MapObject(tName, centerx, centery)
    transform_MapObject(tElevation, centerx, centery)
    transform_MapObject(tLength, centerx, centery)
    transform_MapObject(tDuration, centerx, centery)
    
    
    update_text_object("t_name", f"{name}")
    update_text_object("t_elevation", f"{total_elevation:.2f} hm")
    update_text_object("t_length", f"{total_length:.2f} km")
    update_text_object("t_duration", f"{time_str}")

    if overwriteLength != "":
        update_text_object("t_length", overwriteLength)
    if overwriteHeight != "":
        update_text_object("t_elevation", overwriteHeight)
    if overwriteTime != "":
        update_text_object("t_duration", overwriteTime)

    #Scale text sizes to mm values (blender units)
    bpy.context.view_layer.update()
    current_height = tName.dimensions.y
    if current_height == 0:
        current_height = tElevation.dimensions.y
    if current_height == 0:
        current_height = tLength.dimensions.y
    if current_height == 0:
        current_height = 5
            
    scale_factor = textSize2 / current_height
    tName.scale.x *= scale_factor
    tName.scale.y *= scale_factor

    scale_factor = textSize / current_height
    tElevation.scale.x *= scale_factor
    tLength.scale.x *= scale_factor
    tDuration.scale.x *= scale_factor
    tElevation.scale.y *= scale_factor
    tLength.scale.y *= scale_factor
    tDuration.scale.y *= scale_factor


    
    convert_text_to_mesh("t_name", outerHex.name, False)
    convert_text_to_mesh("t_elevation", outerHex.name, False)
    convert_text_to_mesh("t_length", outerHex.name, False)
    convert_text_to_mesh("t_duration", outerHex.name, False)
    
    
    bpy.ops.object.select_all(action='DESELECT')
    
    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    
    bpy.context.view_layer.objects.active = tName

    
    bpy.ops.object.join()

    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    tName.name = name + "_Text"
    outerHex.name = name + "_Plate"

    tName.location.z += plateThickness
    outerHex.location.z += plateThickness


    #SHAPE ROTATION
    outerHex.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    outerHex.select_set(True)
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)

    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')


    global plateobj
    plateobj = outerHex

    global textobj
    textobj = tName


def HexagonFrontText():


    
    outersize = size * ( 1 + outerBorderSize/100)
    thickness = plateThickness
    textSize = bpy.context.scene.tp3d.textSize
    textSize2 = bpy.context.scene.tp3d.textSizeTitle

    if textSize2 == 0:
        textSize2 = textSize
    
    
    verts = []
    faces = []
    for i in range(6):
        angle = math.radians(60 * i)
        x = outersize/2 * math.cos(angle)
        y = outersize/2 * math.sin(angle)
        verts.append((x, y, 0))
    verts.append((0, 0, 0))  # Center vertex
    faces = [[i, (i + 1) % 6, 6] for i in range(6)]
    mesh = bpy.data.meshes.new("HexagonOuter")
    outerHex = bpy.data.objects.new("HexagonOuter", mesh)
    bpy.context.collection.objects.link(outerHex)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    outerHex.name = name
    outerHex.data.name = name
    
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, -8))#bpy.ops.mesh.select_all(action='DESELECT')

    bpy.ops.object.mode_set(mode='OBJECT')

    # Get the mesh data
    mesh = outerHex.data

    # Get selected faces
    selected_faces = [face for face in mesh.polygons if face.select]
    
    if selected_faces:
        for face in selected_faces:
            for vert_idx in face.vertices:
                vert = mesh.vertices[vert_idx]
                vert.co.z =  - thickness;
    else:
        print("No face selected.")
    
    transform_MapObject(outerHex, centerx, centery)
    
    dist = outersize/2
    
    temp_y = math.sin(math.radians(90)) * (dist  * math.cos(math.radians(30)))
    
    

    for i, (text_name, angle) in enumerate(zip(["t_name","t_length", "t_elevation", "t_duration"], [90 + text_angle_preset, 210 + text_angle_preset, 270 + text_angle_preset, 330 + text_angle_preset])):
        angle_centered = angle + 90
        x = math.cos(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        y = math.sin(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        rot_z = math.radians(angle_centered)
        #if i == 0:
            #rot_z += math.radians(180)
        create_text(text_name, text_name.split("_")[1].capitalize(), (x, y,minThickness/2 - plateThickness / 2),1,  (math.radians(90), 0, rot_z), 0.4)
    
    tName = bpy.data.objects.get("t_name")
    tElevation = bpy.data.objects.get("t_elevation")
    tLength = bpy.data.objects.get("t_length")
    tDuration = bpy.data.objects.get("t_duration")
    
    
    transform_MapObject(tName, centerx, centery)
    transform_MapObject(tElevation, centerx, centery)
    transform_MapObject(tLength, centerx, centery)
    transform_MapObject(tDuration, centerx, centery)
    
    
    update_text_object("t_name", f"{name}")
    update_text_object("t_elevation", f"{total_elevation:.2f} hm")
    update_text_object("t_length", f"{total_length:.2f} km")
    update_text_object("t_duration", f"{time_str}")

    if overwriteLength != "":
        update_text_object("t_length", overwriteLength)
    if overwriteHeight != "":
        update_text_object("t_elevation", overwriteHeight)
    if overwriteTime != "":
        update_text_object("t_duration", overwriteTime)
    
    #Scale text sizes to mm values (blender units)
    bpy.context.view_layer.update()
    current_height = tName.dimensions.y
    if current_height == 0:
        current_height = tElevation.dimensions.y
    if current_height == 0:
        current_height = tLength.dimensions.y
    if current_height == 0:
        current_height = 5
    scale_factor = textSize2 / current_height
    tName.scale.x *= scale_factor
    tName.scale.y *= scale_factor

    scale_factor = textSize / current_height
    tElevation.scale.x *= scale_factor
    tLength.scale.x *= scale_factor
    tDuration.scale.x *= scale_factor
    tElevation.scale.y *= scale_factor
    tLength.scale.y *= scale_factor
    tDuration.scale.y *= scale_factor

    
    convert_text_to_mesh("t_name", outerHex.name, False)
    convert_text_to_mesh("t_elevation", outerHex.name, False)
    convert_text_to_mesh("t_length", outerHex.name, False)
    convert_text_to_mesh("t_duration", outerHex.name, False)
    
    
    bpy.ops.object.select_all(action='DESELECT')
    
    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    
    bpy.context.view_layer.objects.active = tName

    
    bpy.ops.object.join()
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    tName.name = name + "_Text"
    outerHex.name = name + "_Plate"

    tName.location.z += plateThickness
    outerHex.location.z += plateThickness

    #SHAPE ROTATION
    outerHex.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    outerHex.select_set(True)
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')


    global plateobj
    plateobj = outerHex

    global textobj
    textobj = tName

    
def BottomText(obj):
    
    global total_elevation
    global total_length


    name = obj.name
    if "objSize" in obj:
        size = obj["objSize"]
    else:
        return
    
    thickness = 0.1
        # Place text objects
    text_size = (size / 10)
    
    
    dist =  (size/2 - size/2 * (1-pathScale)/2)
    
    temp_y = size/4
    temp_y = 0
    
    
    global additionalExtrusion
    additionalExtrusion = obj["AdditionalExtrusion"]
    
    tName = create_text("t_name", "Name", (0, 0,1.1),text_size)
    

    cx = obj.location.x
    cy = obj.location.y
    
    transform_MapObject(tName, cx, cy)
    
    tName.data.extrude = 0.1
    
    tName.scale.x *= -1

    
    update_text_object("t_name", name)
    
    convert_text_to_mesh("t_name", obj.name, False)
    
    tName.name = name + "_Mark"
    
    bpy.ops.object.select_all(action='DESELECT')

    tName.select_set(True)
    
    bpy.context.view_layer.objects.active = tName

    mat = bpy.data.materials.get("TRAIL")
    tName.data.materials.clear()
    tName.data.materials.append(mat)

    return tName
    

def convert_text_to_mesh(text_obj_name, mesh_obj_name, merge = True):
    # Get the text and mesh objects
    text_obj = bpy.data.objects.get(text_obj_name)
    mesh_obj = bpy.data.objects.get(mesh_obj_name)
    
    if not text_obj or not mesh_obj:
        print("One or both objects not found")
        return
    
    # Ensure the text object is selected and active
    bpy.ops.object.select_all(action='DESELECT')
    text_obj.select_set(True)
    bpy.context.view_layer.objects.active = text_obj
    
    # Convert text to mesh
    bpy.ops.object.convert(target='MESH')
    
    # Enter edit mode
    bpy.ops.object.mode_set(mode='EDIT')
    
    # Enable auto-merge vertices
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.remove_doubles(threshold=0.002)
    #bpy.context.tool_settings.use_mesh_automerge = True
    
    # Switch back to object mode to move it
    bpy.ops.object.mode_set(mode='OBJECT')

    recalculateNormals(text_obj)
    
    # Move the text object up by 1
    text_obj.location.z += 1
    
    # Move the text object down by 1 (merging overlapping vertices)
    text_obj.location.z -= 1
    
    # Disable auto-merge vertices
    bpy.context.tool_settings.use_mesh_automerge = False
    
    if merge == True:
        # Add boolean modifier
        bool_mod = text_obj.modifiers.new(name="Boolean", type='BOOLEAN')
        bool_mod.object = mesh_obj
        bool_mod.operation = 'INTERSECT'
        bool_mod.solver = 'MANIFOLD'

        
        # Apply the boolean modifier
        bpy.ops.object.select_all(action='DESELECT')
        text_obj.select_set(True)
        bpy.context.view_layer.objects.active = text_obj
        bpy.ops.object.modifier_apply(modifier=bool_mod.name)
    
        # Move the text object up by 1
        text_obj.location.z += 0.4

def intersect_alltrails_with_existing_box(cutobject):
    #cutobject is the object that will be cut to the Map shapes
    cutobject.scale.z = 1000


    robj2 = None
    
    bpy.ops.object.select_all(action='DESELECT')
    
    cutobject.select_set(True)
    bpy.context.view_layer.objects.active = cutobject
    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
    
    #cube = bpy.data.objects.get(cutobject)
    cube = cutobject
    if not cube:
        print(f"Object named '{cutobject}' not found.")
        return

    # Get cube's bounding box in world coordinates
    cube_bb = [cube.matrix_world @ Vector(corner) for corner in cube.bound_box]


    def is_point_inside_cube(point, bb):
        min_corner = Vector((min(v[0] for v in bb),
                             min(v[1] for v in bb),
                             min(v[2] for v in bb)))
        max_corner = Vector((max(v[0] for v in bb),
                             max(v[1] for v in bb),
                             max(v[2] for v in bb)))
        return all(min_corner[i] <= point[i] <= max_corner[i] for i in range(3))
    done = False
    boolObjects = []
    for robj in bpy.data.objects:
        if "_Trail" in robj.name and robj.type in {'CURVE', 'MESH'}:
            if not robj.hide_get():
                # Convert curve to mesh
                if robj.type == 'CURVE':
                    bpy.context.view_layer.objects.active = robj
                    bpy.ops.object.select_all(action='DESELECT')
                    robj2 = _debug_preserve_object_if_enabled(
                        robj,
                        _format_debug_step_name("INTERSECT", "CURVE_TO_MESH", "ALLTRAILS"),
                    )
                    if robj2 is None:
                        robj2 = robj.copy()
                        robj2.data = robj.data.copy()
                        bpy.context.collection.objects.link(robj2)
                    robj2.select_set(True)
                    bpy.ops.object.convert(target='MESH')
                    trail_mesh = robj2
                    print("-")
                    print(robj2.name)
                else:
                    trail_mesh = robj
                    print("-")
                    print(robj.name)
                
                #robj.hide_set(True)

                if trail_mesh:
                    if trail_mesh.type == "MESH" and len(trail_mesh.data.vertices) > 0:
                        # Check if any vertex is inside the cube
                        for v in trail_mesh.data.vertices:
                            global_coord = trail_mesh.matrix_world @ v.co
                            if is_point_inside_cube(global_coord, cube_bb):
                                # Apply Boolean modifier
                                #print(f"{trail_mesh.name} is inside the Boundaries")
                                if trail_mesh not in boolObjects:
                                    boolObjects.append(trail_mesh)
                                #Set done to True so it doesnt delete the object later
                                done = True
                                #Change Collection
                                continue  # No need to keep checking this object
                            else:
                                pass
                                #print(f"{trail_mesh.name} is NOT inside the Boundaries")
                    else:
                        print("No Vertices for Trail Found")
                        bpy.data.objects.remove(trail_mesh, do_unlink=True)
                
                #bpy.data.objects.remove(robj, do_unlink=True)
                #break
    if done == False:
        #print("No matching trail found. removing cutobject")
        bpy.data.objects.remove(cutobject, do_unlink=True)
    #Pfade kopieren, zusammenfügen und die boolean operation mit allen trails kombiniert ausführen
    if done == True:
        copied_objects = []
        #Copy objects
        for obj in boolObjects:
            print(f"Copy obj {obj.name}")
            obj_copy = _debug_preserve_object_if_enabled(
                obj,
                _format_debug_step_name("INTERSECT", "BOOLEAN_SOURCES", "ALLTRAILS"),
            )
            if obj_copy is None:
                obj_copy = obj.copy()
                obj_copy.data = obj.data.copy()
                bpy.context.collection.objects.link(obj_copy)
            copied_objects.append(obj_copy)
        
        #Deselect all
        bpy.ops.object.select_all(action='DESELECT')

        #Select all copied objects and make one active
        for obj in copied_objects:
            obj.select_set(True)
        bpy.context.view_layer.objects.active = copied_objects[0]

        #Join them into a single object
        bpy.ops.object.join()

        merged_object = bpy.context.active_object

        bool_mod = cube.modifiers.new(name=f"Intersect", type='BOOLEAN')
        bool_mod.operation = 'INTERSECT'
        bool_mod.object = merged_object
        bpy.context.view_layer.objects.active = cube
        bpy.ops.object.modifier_apply(modifier=bool_mod.name)

        bpy.data.objects.remove(merged_object, do_unlink=True)
        if robj2 != None:
            bpy.data.objects.remove(robj2, do_unlink=True)  

        mat = bpy.data.materials.get("TRAIL")
        cube.data.materials.clear()
        cube.data.materials.append(mat)



        writeMetadata(cube,"TRAIL")


def intersect_trail_with_existing_box(cutobject,trail):
    #cutobject is the object that will be cut to the Map shapes
    cutobject.scale.z = 1000


    robj2 = None
    
    bpy.ops.object.select_all(action='DESELECT')
    
    cutobject.select_set(True)
    bpy.context.view_layer.objects.active = cutobject
    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
    
    #cube = bpy.data.objects.get(cutobject)
    cube = cutobject
    if not cube:
        print(f"Object named '{cutobject}' not found.")
        return

    # Get cube's bounding box in world coordinates
    cube_bb = [cube.matrix_world @ Vector(corner) for corner in cube.bound_box]


    def is_point_inside_cube(point, bb):
        min_corner = Vector((min(v[0] for v in bb),
                             min(v[1] for v in bb),
                             min(v[2] for v in bb)))
        max_corner = Vector((max(v[0] for v in bb),
                             max(v[1] for v in bb),
                             max(v[2] for v in bb)))
        return all(min_corner[i] <= point[i] <= max_corner[i] for i in range(3))
    done = False
    boolObjects = []
    if trail.type == 'CURVE':
        bpy.context.view_layer.objects.active = trail
        bpy.ops.object.select_all(action='DESELECT')
        robj2 = _debug_preserve_object_if_enabled(
            trail,
            _format_debug_step_name("INTERSECT", "CURVE_TO_MESH", "SINGLETRAIL"),
        )
        if robj2 is None:
            robj2 = trail.copy()
            robj2.data = trail.data.copy()
            bpy.context.collection.objects.link(robj2)
        robj2.select_set(True)
        bpy.ops.object.convert(target='MESH')
        trail_mesh = robj2
        print("-")
        print(robj2.name)
    
    #robj.hide_set(True)

    if trail_mesh:
        if trail_mesh.type == "MESH" and len(trail_mesh.data.vertices) > 0:
            # Check if any vertex is inside the cube
            for v in trail_mesh.data.vertices:
                global_coord = trail_mesh.matrix_world @ v.co
                if is_point_inside_cube(global_coord, cube_bb):
                    # Apply Boolean modifier
                    #print(f"{trail_mesh.name} is inside the Boundaries")
                    if trail_mesh not in boolObjects:
                        boolObjects.append(trail_mesh)
                    #Set done to True so it doesnt delete the object later
                    done = True
                    #Change Collection
                    continue  # No need to keep checking this object
                else:
                    pass
                    #print(f"{trail_mesh.name} is NOT inside the Boundaries")
        else:
            print("No Vertices for Trail Found")
            bpy.data.objects.remove(trail_mesh, do_unlink=True)
    

    if done == False:
        #print("No matching trail found. removing cutobject")
        bpy.data.objects.remove(cutobject, do_unlink=True)
    #Pfade kopieren, zusammenfügen und die boolean operation mit allen trails kombiniert ausführen
    if done == True:
        copied_objects = []
        #Copy objects
        for obj in boolObjects:
            print(f"Copy obj {obj.name}")
            obj_copy = _debug_preserve_object_if_enabled(
                obj,
                _format_debug_step_name("INTERSECT", "BOOLEAN_SOURCES", "SINGLETRAIL"),
            )
            if obj_copy is None:
                obj_copy = obj.copy()
                obj_copy.data = obj.data.copy()
                bpy.context.collection.objects.link(obj_copy)
            copied_objects.append(obj_copy)
        
        #Deselect all
        bpy.ops.object.select_all(action='DESELECT')

        #Select all copied objects and make one active
        for obj in copied_objects:
            obj.select_set(True)
        bpy.context.view_layer.objects.active = copied_objects[0]

        #Join them into a single object
        bpy.ops.object.join()

        merged_object = bpy.context.active_object

        bool_mod = cube.modifiers.new(name=f"Intersect", type='BOOLEAN')
        bool_mod.operation = 'INTERSECT'
        bool_mod.object = merged_object
        bpy.context.view_layer.objects.active = cube
        bpy.ops.object.modifier_apply(modifier=bool_mod.name)

        bpy.data.objects.remove(merged_object, do_unlink=True)
        if robj2 != None:
            bpy.data.objects.remove(robj2, do_unlink=True)  

        mat = bpy.data.materials.get("TRAIL")
        cube.data.materials.clear()
        cube.data.materials.append(mat)



        writeMetadata(cube,"TRAIL")

def separate_duplicate_xy(coordinates, offset=0.05):
    seen_xy = set()

    for i, point in enumerate(coordinates):
        # Convert tuple to list if needed
        if isinstance(point, tuple):
            point = list(point)
            coordinates[i] = point  # Update the original array with the list version

        x, y, z = point[0], point[1], point[2]
        xy_key = (x, y,z)

        if xy_key in seen_xy:
            point[2] += offset
            point[1] += offset
            #print("Duplicate")
        else:
            seen_xy.add(xy_key)
    
    return(coordinates)

def apply_boolean_modifier_safely(obj, target_obj, operation, name="Boolean"):
    """Apply a boolean modifier with an EXACT -> MANIFOLD fallback."""
    bool_mod = obj.modifiers.new(name=name, type='BOOLEAN')
    bool_mod.object = target_obj
    bool_mod.operation = operation

    # EXACT is more robust for thin features and near-coplanar geometry.
    for solver in ("EXACT", "MANIFOLD"):
        bool_mod.solver = solver
        try:
            bpy.ops.object.modifier_apply(modifier=bool_mod.name)
            return solver
        except RuntimeError as exc:
            module_logger.warning("Boolean failed on %s with solver=%s: %s", obj.name, solver, exc)
            if bool_mod.name not in obj.modifiers:
                break

    raise RuntimeError(f"Boolean operation '{operation}' failed for object '{obj.name}'")

def _collect_trail_material_indices(mesh_obj):
    trail_indices = set()
    for idx, mat in enumerate(mesh_obj.data.materials):
        if mat and mat.name.upper() == "TRAIL":
            trail_indices.add(idx)
    if not trail_indices and len(mesh_obj.data.materials) > 0:
        trail_indices.add(0)
    return trail_indices

def _sample_trail_cross_sections(mesh_obj, samples=24):
    if mesh_obj.type != "MESH" or len(mesh_obj.data.vertices) == 0:
        return []
    verts_world = [mesh_obj.matrix_world @ v.co for v in mesh_obj.data.vertices]
    min_x = min(v.x for v in verts_world)
    max_x = max(v.x for v in verts_world)
    span = max_x - min_x
    if span <= 1e-6:
        return []
    station_data = []
    tol = max(0.02, span / 400.0)
    for i in range(samples):
        station_x = min_x + (span * i / max(1, samples - 1))
        ys = [v.y for v in verts_world if abs(v.x - station_x) <= tol]
        if len(ys) >= 2:
            width = max(ys) - min(ys)
            station_data.append((i, station_x, width))
    return station_data

def enforce_trail_minimum_width(mesh_obj, target_width, station_samples=24):
    if mesh_obj.type != "MESH" or target_width <= 0:
        return {"measured_min": 0.0, "expanded": False, "post_min": 0.0, "station_count": 0}

    stations = _sample_trail_cross_sections(mesh_obj, samples=station_samples)
    measured_min = min((w for _, _, w in stations), default=0.0)
    trail_mat_indices = _collect_trail_material_indices(mesh_obj)
    deficits = [max(0.0, target_width - w) for _, _, w in stations if w > 0]
    max_deficit = max(deficits, default=0.0)
    expanded = False

    if max_deficit > 0.0:
        expand_amount = (max_deficit * 0.5) + 0.01
        bm = bmesh.new()
        bm.from_mesh(mesh_obj.data)
        bm.faces.ensure_lookup_table()
        geom = []
        for face in bm.faces:
            if face.material_index in trail_mat_indices:
                geom.append(face)
                geom.extend(face.verts)
                geom.extend(face.edges)
        if geom:
            trail_faces = [f for f in bm.faces if f.material_index in trail_mat_indices]
            bmesh.ops.solidify(
                bm,
                geom=trail_faces,
                thickness=expand_amount,
            )
            bm.to_mesh(mesh_obj.data)
            expanded = True
        bm.free()
        if expanded:
            recalculateNormals(mesh_obj)
            try:
                delete_non_manifold(mesh_obj)
            except Exception as exc:
                module_logger.warning("Non-manifold cleanup failed for %s: %s", mesh_obj.name, exc)

    post_stations = _sample_trail_cross_sections(mesh_obj, samples=station_samples)
    post_min = min((w for _, _, w in post_stations), default=0.0)
    if post_min + 1e-6 < target_width:
        module_logger.warning(
            "Trail width safety net failed for %s: target=%.4f, measured=%.4f",
            mesh_obj.name,
            target_width,
            post_min,
        )
    else:
        module_logger.info(
            "Trail width safety net ok for %s: target=%.4f, measured=%.4f",
            mesh_obj.name,
            target_width,
            post_min,
        )
    return {
        "measured_min": measured_min,
        "expanded": expanded,
        "post_min": post_min,
        "station_count": len(post_stations),
    }

def single_color_mode(crv, mapName):



    map = bpy.data.objects.get(mapName)
    tol = bpy.context.scene.tp3d.tolerance
    print(f"tol: {tol}")
    print (crv.name)
    print(crv.type)

    lowestZonCurve = 1000

    if crv.type == "CURVE":
        
        #Getting the lowest Point of the Curve
        curve = crv.data
        for spline in curve.splines:
            if hasattr(spline, "points") and len(spline.points) > 0:
                for p in spline.points:
                    co_local = Vector((p.co.x, p.co.y, p.co.z))
                    co_world = crv.matrix_world @ co_local
                    z = co_local.z
                    if lowestZonCurve is None or z < lowestZonCurve:
                        lowestZonCurve = z

        print(f"lowestzoncurve: {lowestZonCurve}")


        crv_data = crv.data
        crv_data.dimensions = "2D"
        crv_data.dimensions = "3D"
        crv_data.extrude = 200


        # Ensure the text object is selected and active
        bpy.ops.object.select_all(action='DESELECT')
        crv.select_set(True)
        bpy.context.view_layer.objects.active = crv

        bpy.ops.object.mode_set(mode='EDIT')

        # select all points if you want to smooth everything
        bpy.ops.curve.select_all(action='SELECT')

        # run the smooth operator   
        bpy.ops.curve.smooth()

        # back to Object Mode if you like
        bpy.ops.object.mode_set(mode='OBJECT')

        #Create a duplicate object of the curve that will be slightly thicker
        crv_thick = crv.copy()
        crv_thick.data = crv.data.copy()
        crv_thick.data.bevel_depth = pathThickness/2 + tol  # Set the thickness of the curve
        bpy.context.collection.objects.link(crv_thick)
    elif crv.type == "MESH":
        
        depsgraph = bpy.context.evaluated_depsgraph_get()
        eval_obj = crv.evaluated_get(depsgraph)
        mesh = eval_obj.to_mesh()
        lowestZonCurve = min((crv.matrix_world @ v.co).z for v in mesh.vertices)

        #crv.scale.z = 100

        crv_thick = crv.copy()
        crv_thick.data = crv.data.copy()
        #crv_thick.data.scale = 1.02
        bpy.context.collection.objects.link(crv_thick)

    bpy.ops.object.convert(target='MESH')

    recalculateNormals(crv)

    apply_boolean_modifier_safely(crv, map, 'INTERSECT', name="TrailIntersect_1")

    for v in crv.data.vertices:
        pass
        v.co += Vector((0,0,lowestZonCurve - 2))

    recalculateNormals(crv)


    #Adding another Intersect Modifier to make the path "Plane" with the Map
    recalculateNormals(crv)

    apply_boolean_modifier_safely(crv, map, 'INTERSECT', name="TrailIntersect_2")
    safety_metrics = enforce_trail_minimum_width(crv, pathThickness, station_samples=28)
    module_logger.info(
        "Trail safety metrics for %s: sampled_stations=%d, pre_min=%.4f, post_min=%.4f, expanded=%s",
        crv.name,
        safety_metrics["station_count"],
        safety_metrics["measured_min"],
        safety_metrics["post_min"],
        safety_metrics["expanded"],
    )
    if safety_metrics["expanded"]:
        apply_boolean_modifier_safely(crv, map, 'INTERSECT', name="TrailIntersect_Safety")

    #doing the same for the duplicate
    bpy.ops.object.select_all(action='DESELECT')
    crv_thick.select_set(True)
    bpy.context.view_layer.objects.active = crv_thick
    bpy.ops.object.convert(target='MESH')


    apply_boolean_modifier_safely(crv_thick, map, 'INTERSECT', name="TrailIntersect_Thick")

    bpy.ops.object.origin_set(type='ORIGIN_GEOMETRY', center='BOUNDS')
    crv_thick.scale = (1.002,1.002,1)

    recalculateNormals(crv_thick)

    # Move the text object up by x
    crv_thick.location.z += lowestZonCurve -2

    bpy.ops.object.select_all(action='DESELECT')
    map.select_set(True)
    bpy.context.view_layer.objects.active = map

    #Remove the last material from the MAP as the boolean operation adds it to the list witout using it
    #Without removing it will color the next boolean operation in the color of the trail
    mats = map.data.materials

    apply_boolean_modifier_safely(map, crv_thick, "DIFFERENCE", name="TrailDifference")
    bpy.data.objects.remove(crv_thick, do_unlink = True)



# --- OSM FETCHING ---

def _osm_selector_lines(kind, south, west, north, east):
    if kind == "WATER":
        return [
            f'nwr["natural"="water"]({south},{west},{north},{east});',
            f'nwr["water"="lake"]({south},{west},{north},{east});',
            f'nwr["waterway"="river"]({south},{west},{north},{east});',
            f'nwr["waterway"="stream"]({south},{west},{north},{east});',
            f'nwr["waterway"="canal"]({south},{west},{north},{east});',
        ]
    if kind == "FOREST":
        return [
            f'nwr["natural"="wood"]({south},{west},{north},{east});',
            f'nwr["landuse"="forest"]({south},{west},{north},{east});',
        ]
    if kind == "CITY":
        return [f'nwr["landuse"~"residential|urban|commercial|industrial"]({south},{west},{north},{east});']
    if kind == "GLACIER":
        return [f'nwr["natural"="glacier"]({south},{west},{north},{east});']
    return []


def _build_osm_data_query(kind, bbox):
    south, west, north, east = bbox
    selectors = "\n            ".join(_osm_selector_lines(kind, south, west, north, east))
    return f"""
        [out:json][timeout:25];
        (
            {selectors}
        );
        out body;
        >;
        out skel qt;
        """


def derive_osm_tile_size_from_scale(bbox, terrain_subdivisions=4, horizontal_scale=1.0):
    south, west, north, east = bbox
    lat_span = max(0.001, abs(north - south))
    lon_span = max(0.001, abs(east - west))
    subdiv_factor = max(1, int(terrain_subdivisions) + 1)
    scale_factor = max(0.25, min(4.0, float(horizontal_scale) if horizontal_scale else 1.0))
    target_lat = max(0.01, min(2.0, lat_span / math.sqrt(subdiv_factor) * (1.0 / scale_factor)))
    target_lon = max(0.01, min(2.0, lon_span / math.sqrt(subdiv_factor) * (1.0 / scale_factor)))
    return target_lat, target_lon


def _subdivide_bbox_grid(bbox, lat_step, lon_step):
    south, west, north, east = bbox
    tiles = []
    lat = south
    while lat < north:
        next_lat = min(north, lat + lat_step)
        lon = west
        while lon < east:
            next_lon = min(east, lon + lon_step)
            tiles.append((lat, lon, next_lat, next_lon))
            lon = next_lon
        lat = next_lat
    return tiles


def fetch_osm_query(query, kind="WATER", overpass_endpoints=None, connect_timeout=5, read_timeout=30, max_retries=3, base_backoff_seconds=1.0):
    endpoints = overpass_endpoints or [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
    ]
    headers = {
        "User-Agent": "TrailPrint3D/2.52 (OSM Overpass client)",
        "Accept": "application/json,text/plain,*/*",
    }
    result = {"ok": False, "status_code": None, "error_type": None, "payload_size_bytes": 0, "json_data": None, "endpoint": None}
    for endpoint in endpoints:
        for attempt in range(max_retries + 1):
            try:
                response = requests.post(endpoint, data={'data': query}, headers=headers, timeout=(connect_timeout, read_timeout))
                result["status_code"] = response.status_code
                result["payload_size_bytes"] = len(response.content or b"")
                result["endpoint"] = endpoint
                try:
                    response_json = response.json()
                except ValueError:
                    result["error_type"] = "json_parse_error"
                    response_json = None
                if response.status_code == 200 and response_json is not None:
                    result["ok"] = True
                    result["json_data"] = response_json
                    result["error_type"] = None
                    return result
                if response.status_code in (406, 408, 425, 429) or response.status_code >= 500:
                    sleep_for = base_backoff_seconds * (2 ** attempt) + random.uniform(0, 0.5)
                    time.sleep(sleep_for)
                    continue
                result["error_type"] = f"http_{response.status_code}"
                return result
            except requests.exceptions.RequestException:
                result["error_type"] = "network_exception"
                if attempt >= max_retries:
                    break
                time.sleep(base_backoff_seconds * (2 ** attempt) + random.uniform(0, 0.5))
    return result


def _probe_osm_payload(bbox, kind, overpass_endpoints=None, connect_timeout=5, read_timeout=15):
    south, west, north, east = bbox
    selectors = "\n            ".join(_osm_selector_lines(kind, south, west, north, east))
    probe_query = f"""
        [out:json][timeout:20];
        (
            {selectors}
        );
        out count;
    """
    resp = fetch_osm_query(probe_query, kind=f"{kind}_PROBE", overpass_endpoints=overpass_endpoints, connect_timeout=connect_timeout, read_timeout=read_timeout, max_retries=2)
    total = 0
    if resp.get("ok"):
        elems = (resp.get("json_data") or {}).get("elements", [])
        if elems and isinstance(elems[0], dict):
            total = int((elems[0].get("tags") or {}).get("total", 0) or 0)
    return {"ok": resp.get("ok", False), "element_count": total, "estimated_bytes": total * 350}

@log_workflow
def fetch_osm_data(
    bbox,
    kind = "WATER",
    overpass_endpoints=None,
    connect_timeout=5,
    read_timeout=30,
    max_retries=3,
    base_backoff_seconds=1.0,
):
    query = _build_osm_data_query(kind, bbox)
    return fetch_osm_query(
        query,
        kind=kind,
        overpass_endpoints=overpass_endpoints,
        connect_timeout=connect_timeout,
        read_timeout=read_timeout,
        max_retries=max_retries,
        base_backoff_seconds=base_backoff_seconds,
    )


def extract_multipolygon_bodies(elements, nodes):

    # Helper to get coordinates of a way by its node ids
    def way_coords(way):
        return [ (nodes[nid]['lat'], nodes[nid]['lon'], nodes[nid].get('elevation', 0)) for nid in way['nodes'] if nid in nodes ]

    # Store multipolygons as records with outer and inner rings.
    multipolygon_lakes = []

    # Index ways by their id for quick lookup
    way_dict = {el['id']: el for el in elements if el['type'] == 'way'}

    for el in elements:
        if el['type'] in ('relation', 'way'):
            # Collect outer and inner member ways
            outer_ways = []
            inner_ways = []

            for member in el.get('members', []):
                if member['type'] != 'way':
                    continue
                way = way_dict.get(member['ref'])
                if not way:
                    continue

                role = member.get('role', '')
                if role == 'outer':
                    outer_ways.append(way)
                elif role == 'inner':
                    inner_ways.append(way)

            # Stitch ways to closed loops for outer and inner rings
            def stitch_ways(ways):
                loops = []
                # Convert ways to list of coords
                ways_coords = [way_coords(w) for w in ways]

                while ways_coords:
                    current = ways_coords.pop(0)
                    changed = True
                    while changed:
                        changed = False
                        i = 0
                        while i < len(ways_coords):
                            w = ways_coords[i]

                            # Check if current end connects to w start or end
                            if w:
                                if current[-1] == w[0]:
                                    current.extend(w[1:])
                                    ways_coords.pop(i)
                                    changed = True
                                elif current[-1] == w[-1]:
                                    current.extend(reversed(w[:-1]))
                                    ways_coords.pop(i)
                                    changed = True
                                # Also check if current start connects to w end or start
                                elif current[0] == w[-1]:
                                    current = w[:-1] + current
                                    ways_coords.pop(i)
                                    changed = True
                                elif current[0] == w[0]:
                                    current = list(reversed(w[1:])) + current
                                    ways_coords.pop(i)
                                    changed = True
                                else:
                                    i += 1
                    loops.append(current)

                return loops

            outer_loops = stitch_ways(outer_ways)
            inner_loops = stitch_ways(inner_ways)

            if outer_loops or inner_loops:
                multipolygon_lakes.append({
                    "relation_id": el.get("id"),
                    "outers": outer_loops,
                    "inners": inner_loops,
                })

    return multipolygon_lakes



# --- COLOR MESH CREATION ---

def col_create_line_mesh(name, coords):
    mesh = bpy.data.meshes.new(name)
    tobj = bpy.data.objects.new(name, mesh)
    bpy.context.collection.objects.link(tobj)

    bm = bmesh.new()
    verts = [bm.verts.new(c) for c in coords]
    for i in range(len(verts) - 1):
        bm.edges.new((verts[i], verts[i + 1]))
    bm.to_mesh(mesh)
    bm.free()
    _debug_preserve_created_object_if_enabled(tobj, creation_type="LINE")
    return tobj


def col_create_face_mesh(name, coords):

    if len(coords) < 3:
        return  # Need at least 3 points for a face


    mesh = bpy.data.meshes.new(name)
    tobj = bpy.data.objects.new(name, mesh)
    bpy.context.collection.objects.link(tobj)

    bm = bmesh.new()
    # Multipolygon rings are often explicitly closed (first point == last point).
    # Remove duplicate closing vertex before face creation to avoid invalid ngons.
    face_coords = list(coords)
    if len(face_coords) > 1 and face_coords[0] == face_coords[-1]:
        face_coords = face_coords[:-1]

    if len(face_coords) < 3:
        bm.free()
        _debug_preserve_created_object_if_enabled(tobj, creation_type="FACE")
        return tobj

    verts = [bm.verts.new(c) for c in face_coords]
    try:
        bm.faces.new(verts)
    except ValueError:
        # Fallback for concave/complex rings where direct ngon creation fails.
        # Build boundary edges and let Blender triangulate/fill the polygon.
        edges = []
        for i in range(len(verts)):
            v0 = verts[i]
            v1 = verts[(i + 1) % len(verts)]
            try:
                edges.append(bm.edges.new((v0, v1)))
            except ValueError:
                # Edge may already exist.
                pass
        if edges:
            try:
                bmesh.ops.triangle_fill(bm, edges=edges, use_beauty=True, use_dissolve=True)
            except Exception:
                pass
    if not bm.faces:
        bm.free()
        bpy.data.objects.remove(tobj, do_unlink=True)
        if mesh.users == 0:
            bpy.data.meshes.remove(mesh)
        return None
    bm.to_mesh(mesh)
    bm.free()
    _debug_preserve_created_object_if_enabled(tobj, creation_type="FACE")
    return tobj

def col_create_face_mesh_with_holes(name, outer_coords, assigned_inners, relation_id=None, outer_idx=None):
    candidate_holes = len(assigned_inners or [])
    telemetry = {
        "candidate_holes": candidate_holes,
        "holes_applied": 0,
        "boolean_changed_mesh": False,
        "delta_faces": 0,
        "delta_edges": 0,
        "prep": 0.0,
        "apply": 0.0,
        "source": "bmesh_edgenet_hole_apply",
    }

    prep_started = time.perf_counter()
    mesh = bpy.data.meshes.new(name)
    tobj = bpy.data.objects.new(name, mesh)
    bpy.context.collection.objects.link(tobj)

    bm = bmesh.new()

    def _build_loop_edges(loop_coords):
        coords = list(loop_coords)
        if len(coords) > 1 and coords[0] == coords[-1]:
            coords = coords[:-1]
        if len(coords) < 3:
            return []
        verts = [bm.verts.new(c) for c in coords]
        edges = []
        for i in range(len(verts)):
            v0 = verts[i]
            v1 = verts[(i + 1) % len(verts)]
            try:
                edges.append(bm.edges.new((v0, v1)))
            except ValueError:
                pass
        return edges

    outer_valid, outer_reason = classify_ring_validity(outer_coords, 0.0)
    if not outer_valid:
        module_logger.warning(
            "Hole bmesh outer rejected relation=%s outer_idx=%s reason=%s",
            relation_id,
            outer_idx,
            outer_reason,
        )
        bm.free()
        bpy.data.objects.remove(tobj, do_unlink=True)
        if mesh.users == 0:
            bpy.data.meshes.remove(mesh)
        telemetry["prep"] = time.perf_counter() - prep_started
        return None, telemetry

    all_edges = []
    all_edges.extend(_build_loop_edges(outer_coords))

    valid_inners = []
    for inner_idx, inner_coords in enumerate(assigned_inners or []):
        inner_valid, inner_reason = classify_ring_validity(inner_coords, 0.0)
        if not inner_valid:
            module_logger.warning(
                "Hole bmesh inner rejected relation=%s outer_idx=%s inner_idx=%s reason=%s",
                relation_id,
                outer_idx,
                inner_idx,
                inner_reason,
            )
            continue
        valid_inners.append(inner_coords)
        all_edges.extend(_build_loop_edges(inner_coords))

    telemetry["holes_applied"] = len(valid_inners)

    if all_edges:
        try:
            bmesh.ops.edgenet_prepare(bm, edges=all_edges)
        except Exception:
            pass
        bmesh.ops.triangle_fill(bm, edges=all_edges, use_beauty=True, use_dissolve=False)

    to_delete = []
    for face in bm.faces:
        c = face.calc_center_median()
        cxy = (c.x, c.y)
        if not _point_in_ring_2d(cxy, outer_coords):
            to_delete.append(face)
            continue
        for inner in valid_inners:
            if _point_in_ring_2d(cxy, inner):
                to_delete.append(face)
                break

    if to_delete:
        bmesh.ops.delete(bm, geom=to_delete, context='FACES')

    pre_faces = len(bm.faces)
    pre_edges = len(bm.edges)

    bmesh.ops.dissolve_limit(bm, angle_limit=0.001, verts=bm.verts, edges=bm.edges)

    telemetry["delta_faces"] = len(bm.faces) - pre_faces
    telemetry["delta_edges"] = len(bm.edges) - pre_edges
    telemetry["boolean_changed_mesh"] = telemetry["holes_applied"] > 0
    telemetry["prep"] = time.perf_counter() - prep_started

    if not bm.faces:
        bm.free()
        bpy.data.objects.remove(tobj, do_unlink=True)
        if mesh.users == 0:
            bpy.data.meshes.remove(mesh)
        return None, telemetry

    bm.to_mesh(mesh)
    bm.free()
    _debug_preserve_created_object_if_enabled(tobj, creation_type="FACE")
    return tobj, telemetry


def calculate_polygon_area_2d(coords):
    area = 0.0
    
    if len(coords) >= 3:
    
        n = len(coords)
        for i in range(n):
            x0, y0, z0 = coords[i]
            x1, y1, z1 = coords[(i + 1) % n]  # Wrap around to the first point
            area += (x0 * y1) - (x1 * y0)
    
    return abs(area) * 0.5


def _ring_bbox_2d(coords):
    if not coords:
        return None
    xs = [p[0] for p in coords]
    ys = [p[1] for p in coords]
    return (min(xs), min(ys), max(xs), max(ys))


def _segments_intersect_2d(a1, a2, b1, b2, epsilon=1e-9):
    ax1, ay1 = a1[0], a1[1]
    ax2, ay2 = a2[0], a2[1]
    bx1, by1 = b1[0], b1[1]
    bx2, by2 = b2[0], b2[1]

    def orient(px, py, qx, qy, rx, ry):
        return (qx - px) * (ry - py) - (qy - py) * (rx - px)

    def on_segment(px, py, qx, qy, rx, ry):
        return (min(px, rx) - epsilon <= qx <= max(px, rx) + epsilon and
                min(py, ry) - epsilon <= qy <= max(py, ry) + epsilon)

    o1 = orient(ax1, ay1, ax2, ay2, bx1, by1)
    o2 = orient(ax1, ay1, ax2, ay2, bx2, by2)
    o3 = orient(bx1, by1, bx2, by2, ax1, ay1)
    o4 = orient(bx1, by1, bx2, by2, ax2, ay2)

    if ((o1 > epsilon and o2 < -epsilon) or (o1 < -epsilon and o2 > epsilon)) and \
       ((o3 > epsilon and o4 < -epsilon) or (o3 < -epsilon and o4 > epsilon)):
        return True

    if abs(o1) <= epsilon and on_segment(ax1, ay1, bx1, by1, ax2, ay2):
        return True
    if abs(o2) <= epsilon and on_segment(ax1, ay1, bx2, by2, ax2, ay2):
        return True
    if abs(o3) <= epsilon and on_segment(bx1, by1, ax1, ay1, bx2, by2):
        return True
    if abs(o4) <= epsilon and on_segment(bx1, by1, ax2, ay2, bx2, by2):
        return True
    return False


def is_ring_simple_2d(coords):
    if len(coords) < 4:
        return False

    segment_count = len(coords) - 1
    for i in range(segment_count):
        a1 = coords[i]
        a2 = coords[i + 1]
        for j in range(i + 1, segment_count):
            if j == i + 1:
                continue
            if i == 0 and j == segment_count - 1:
                continue
            b1 = coords[j]
            b2 = coords[j + 1]
            if _segments_intersect_2d(a1, a2, b1, b2):
                return False
    return True




def _compute_effective_min_area(kind, base_area):
    threshold = max(1e-9, float(base_area or 0.0))
    if kind != "WATER":
        return threshold

    try:
        bbox = (minLat, minLon, maxLat, maxLon)
        south_west = convert_to_blender_coordinates(bbox[0], bbox[1], 0, 0)
        north_east = convert_to_blender_coordinates(bbox[2], bbox[3], 0, 0)
        width = abs(north_east[0] - south_west[0])
        height = abs(north_east[1] - south_west[1])
        map_extent_area = max(1e-9, width * height)
    except Exception:
        map_extent_area = 0.0

    # Dynamic floor for tiny sliver polygons. Scales with map extent and horizontal scale.
    # Higher detail scales (larger scaleHor) permit proportionally smaller features.
    scale_factor = max(1.0, float(scaleHor) if scaleHor else 1.0)
    extent_floor = (map_extent_area / (35000.0 * scale_factor)) if map_extent_area > 0 else 0.0
    return max(threshold, extent_floor)


def _remove_small_mesh_islands(obj, min_area_threshold):
    if not obj or obj.type != 'MESH' or not obj.data:
        return 0, None

    bm = bmesh.new()
    bm.from_mesh(obj.data)
    bm.faces.ensure_lookup_table()
    bm.verts.ensure_lookup_table()

    face_tags = set()
    dropped = 0
    kept_areas = []

    for face in bm.faces:
        face.tag = False

    for face in bm.faces:
        if face.index in face_tags:
            continue
        stack = [face]
        island_faces = []
        island_face_area = 0.0
        while stack:
            f = stack.pop()
            if f.index in face_tags:
                continue
            face_tags.add(f.index)
            island_faces.append(f)
            fa = f.calc_area()
            island_face_area += fa
            for edge in f.edges:
                for linked in edge.link_faces:
                    if linked.index not in face_tags:
                        stack.append(linked)

        if island_face_area < min_area_threshold:
            dropped += 1
            for f in island_faces:
                f.tag = True
        else:
            kept_areas.append(island_face_area)

    if any(f.tag for f in bm.faces):
        bmesh.ops.delete(bm, geom=[f for f in bm.faces if f.tag], context='FACES')
        bm.to_mesh(obj.data)
        obj.data.update()

    bm.free()
    return dropped, (min(kept_areas) if kept_areas else None)

def classify_ring_validity(coords, min_area=0.0):
    if not coords:
        return False, "empty"
    if coords[0] != coords[-1]:
        return False, "not_closed"
    if len(coords) < 4:
        return False, "too_few_points"
    if not is_ring_simple_2d(coords):
        return False, "self_intersecting"
    area = calculate_polygon_area_2d(coords)
    if area <= min_area:
        return False, "area_below_threshold"
    return True, "ok"


def _is_valid_ring(coords, min_area=0.0):
    is_valid, _ = classify_ring_validity(coords, min_area=min_area)
    return is_valid


def _normalize_ring_for_validation(coords, close_tolerance=1e-5):
    if not coords:
        return []

    deduped = [coords[0]]
    for pt in coords[1:]:
        if pt != deduped[-1]:
            deduped.append(pt)

    if len(deduped) >= 2:
        x0, y0, z0 = deduped[0]
        x1, y1, z1 = deduped[-1]
        if deduped[0] != deduped[-1]:
            dx = x1 - x0
            dy = y1 - y0
            dz = z1 - z0
            if (dx * dx + dy * dy + dz * dz) <= (close_tolerance * close_tolerance):
                deduped.append(deduped[0])

    return deduped


def _validate_ring_with_reason(coords, min_area=0.0):
    if not coords:
        return False, 0.0, "too_few_points"
    if coords[0] != coords[-1]:
        return False, 0.0, "not_closed"
    if len(coords) < 4:
        return False, 0.0, "too_few_points"
    if not is_ring_simple_2d(coords):
        return False, 0.0, "self_intersecting"
    area = calculate_polygon_area_2d(coords)
    if area <= min_area:
        return False, area, "area_below_threshold"
    return True, area, None


def _ring_bbox_2d(coords):
    if not coords:
        return None
    xs = [p[0] for p in coords]
    ys = [p[1] for p in coords]
    return (min(xs), min(ys), max(xs), max(ys))


def _ring_centroid_2d(coords):
    if not coords:
        return None
    pts = coords[:-1] if len(coords) > 1 and coords[0] == coords[-1] else coords
    if not pts:
        return None
    sx = sum(p[0] for p in pts)
    sy = sum(p[1] for p in pts)
    n = len(pts)
    return (sx / n, sy / n)


def _point_in_ring_2d(point, ring):
    if not point or not ring or len(ring) < 4:
        return False
    x, y = point
    inside = False
    pts = ring[:-1] if ring[0] == ring[-1] else ring
    n = len(pts)
    for i in range(n):
        x0, y0, _ = pts[i]
        x1, y1, _ = pts[(i + 1) % n]
        intersects = ((y0 > y) != (y1 > y)) and (x < (x1 - x0) * (y - y0) / ((y1 - y0) or 1e-12) + x0)
        if intersects:
            inside = not inside
    return inside


def _sanitize_water_outer_mesh(obj, merge_distance=1e-6):
    actions = []
    if not obj or obj.type != "MESH" or not obj.data:
        return actions

    mesh = obj.data
    bm = bmesh.new()
    bm.from_mesh(mesh)

    try:
        before_verts = len(bm.verts)
        bmesh.ops.remove_doubles(bm, verts=bm.verts, dist=merge_distance)
        merged = max(0, before_verts - len(bm.verts))
        actions.append({"action": "remove_doubles", "merge_distance": merge_distance, "merged_verts": merged})

        loose_geom = [e for e in bm.edges if len(e.link_faces) == 0] + [v for v in bm.verts if len(v.link_edges) == 0]
        if loose_geom:
            bmesh.ops.delete(bm, geom=loose_geom, context="VERTS")
        actions.append({"action": "delete_loose", "deleted_items": len(loose_geom)})

        zero_area_faces = [f for f in bm.faces if f.calc_area() <= 1e-12]
        if zero_area_faces:
            bmesh.ops.dissolve_faces(bm, faces=zero_area_faces)
        actions.append({"action": "dissolve_zero_area_faces", "faces_targeted": len(zero_area_faces)})

        if bm.faces:
            bmesh.ops.recalc_face_normals(bm, faces=list(bm.faces))
        actions.append({"action": "recalc_normals", "faces": len(bm.faces)})

        bm.to_mesh(mesh)
        mesh.update()
    finally:
        bm.free()

    return actions


def _mesh_health_stats(obj):
    stats = {
        "faces": 0,
        "edges": 0,
        "verts": 0,
        "non_manifold_edges": 0,
        "loose_edges": 0,
        "zero_area_faces": 0,
        "min_face_area": 0.0,
        "max_face_area": 0.0,
    }
    if not obj or obj.type != "MESH" or not obj.data:
        return stats
    mesh = obj.data
    stats["faces"] = len(mesh.polygons)
    stats["edges"] = len(mesh.edges)
    stats["verts"] = len(mesh.vertices)
    areas = []
    for poly in mesh.polygons:
        area = float(poly.area)
        areas.append(area)
        if area <= 1e-12:
            stats["zero_area_faces"] += 1
    if areas:
        stats["min_face_area"] = min(areas)
        stats["max_face_area"] = max(areas)
    edge_face_counts = {}
    for poly in mesh.polygons:
        for edge_key in poly.edge_keys:
            edge_face_counts[edge_key] = edge_face_counts.get(edge_key, 0) + 1

    for edge in mesh.edges:
        # MeshEdge (bpy.types.MeshEdge) does not expose link_faces.
        # Build adjacency from polygon edge keys instead.
        edge_key = tuple(sorted(edge.vertices))
        linked = edge_face_counts.get(edge_key, 0)
        if linked != 2:
            stats["non_manifold_edges"] += 1
        if linked == 0:
            stats["loose_edges"] += 1
    return stats




def _get_or_create_temp_debug_root_collection():
    coll_name = "Temporary objects"
    coll = bpy.data.collections.get(coll_name)
    if not coll:
        coll = bpy.data.collections.new(coll_name)

    scene_coll = bpy.context.scene.collection
    if coll.name not in scene_coll.children:
        scene_coll.children.link(coll)

    return coll


def _sanitize_temp_debug_collection_name(step_name: str, max_len: int = 63):
    safe_name = bpy.path.clean_name(step_name or "step")
    return (safe_name or "step")[:max_len]


def _format_debug_step_name(phase: str, action: str, variant: str = ""):
    tokens = [phase, action, variant]
    normalized_tokens = []
    for token in tokens:
        if not token:
            continue
        clean = bpy.path.clean_name(str(token)).upper()
        if clean:
            normalized_tokens.append(clean)
    return "_".join(normalized_tokens) or "STEP_UNSPECIFIED"


def _get_or_create_temp_debug_step_collection(step_name: str):
    root_coll = _get_or_create_temp_debug_root_collection()
    coll_name = _sanitize_temp_debug_collection_name(step_name)

    step_coll = root_coll.children.get(coll_name)
    if not step_coll:
        step_coll = bpy.data.collections.get(coll_name)
        if step_coll and step_coll.name not in root_coll.children:
            root_coll.children.link(step_coll)
        if not step_coll:
            step_coll = bpy.data.collections.new(coll_name)
            root_coll.children.link(step_coll)

    return step_coll


_TP3D_DEBUG_SNAPSHOT_COUNTER = 0


def _snapshot_object_to_temp_collection(obj, step_name: str, suffix: str = "", kind: str = ""):
    global _TP3D_DEBUG_SNAPSHOT_COUNTER
    if not _is_valid_blender_object(obj):
        return None

    dup_obj = obj.copy()
    if hasattr(obj, "data") and obj.data is not None and hasattr(obj.data, "copy"):
        dup_obj.data = obj.data.copy()

    safe_step = _sanitize_temp_debug_collection_name(step_name)
    safe_suffix = bpy.path.clean_name(suffix) if suffix else ""
    dup_name = f"{obj.name}_tmp_{safe_step}"
    if safe_suffix:
        dup_name = f"{dup_name}_{safe_suffix}"
    dup_obj.name = dup_name[:63]
    _TP3D_DEBUG_SNAPSHOT_COUNTER += 1
    dup_obj["tp3d_debug_source_object"] = obj.name
    dup_obj["tp3d_debug_step"] = safe_step
    dup_obj["tp3d_debug_timestamp"] = f"{int(time.time())}:{_TP3D_DEBUG_SNAPSHOT_COUNTER}"
    if kind:
        dup_obj["tp3d_debug_kind"] = str(kind)

    step_coll = _get_or_create_temp_debug_step_collection(step_name)
    step_coll.objects.link(dup_obj)
    return dup_obj


def _debug_preserve_object_if_enabled(obj, step_name, suffix="", kind=""):
    props = getattr(bpy.context.scene, "tp3d", None)
    if not props or not getattr(props, "debug_keep_temporary_objects", False):
        return None
    return _snapshot_object_to_temp_collection(obj, step_name, suffix=suffix, kind=kind)


def _debug_preserve_created_object_if_enabled(obj, creation_type="MESH"):
    """Capture newly-created objects in the temporary debug collections."""
    if not _is_valid_blender_object(obj):
        return None
    step_name = _format_debug_step_name("CREATE", creation_type, obj.name)
    return _debug_preserve_object_if_enabled(obj, step_name, suffix="CREATED", kind=creation_type)


def _get_or_create_hole_temp_collection():
    coll_name = "_TP3D_HoleTemp"
    coll = bpy.data.collections.get(coll_name)
    if not coll:
        coll = bpy.data.collections.new(coll_name)
    scene_coll = bpy.context.scene.collection
    if coll.name not in scene_coll.children:
        scene_coll.children.link(coll)
    return coll


def _create_combined_hole_cutter(name, hole_rings, temp_collection):
    bm = bmesh.new()
    valid_count = 0
    for ring in hole_rings:
        if not _is_valid_ring(ring):
            continue
        ring_no_close = ring[:-1]
        if len(ring_no_close) < 3:
            continue
        verts = [bm.verts.new(c) for c in ring_no_close]
        try:
            bm.faces.new(verts)
            valid_count += 1
        except ValueError:
            pass

    if valid_count == 0:
        bm.free()
        return None, 0

    mesh = bpy.data.meshes.new(name)
    bm.to_mesh(mesh)
    bm.free()

    hole_obj = bpy.data.objects.new(name, mesh)
    temp_collection.objects.link(hole_obj)
    return hole_obj, valid_count


def apply_hole_difference(outer_obj, hole_rings, name_prefix="Hole"):
    prep_started = time.perf_counter()
    candidate_holes = len(hole_rings)
    temp_collection = _get_or_create_hole_temp_collection()
    hole_obj, holes_applied = _create_combined_hole_cutter(f"{name_prefix}_combined", hole_rings, temp_collection)
    prep_elapsed = time.perf_counter() - prep_started

    telemetry = {
        "candidate_holes": candidate_holes,
        "cutter_faces_created": holes_applied,
        "boolean_changed_mesh": False,
        "delta_faces": 0,
        "delta_edges": 0,
        "prep": prep_elapsed,
        "apply": 0.0,
    }

    if not hole_obj:
        return telemetry

    outer_mesh = outer_obj.data
    pre_faces = len(outer_mesh.polygons)
    pre_edges = len(outer_mesh.edges)
    pre_verts = len(outer_mesh.vertices)

    apply_started = time.perf_counter()
    bool_mod = outer_obj.modifiers.new(name=f"{name_prefix}_diff", type='BOOLEAN')
    bool_mod.operation = 'DIFFERENCE'
    bool_mod.solver = 'EXACT'
    bool_mod.object = hole_obj

    ctx = bpy.context
    bpy.ops.object.select_all(action='DESELECT')
    outer_obj.select_set(True)
    ctx.view_layer.objects.active = outer_obj
    bpy.ops.object.modifier_apply(modifier=bool_mod.name)
    apply_elapsed = time.perf_counter() - apply_started

    post_faces = len(outer_mesh.polygons)
    post_edges = len(outer_mesh.edges)
    post_verts = len(outer_mesh.vertices)

    telemetry["delta_faces"] = post_faces - pre_faces
    telemetry["delta_edges"] = post_edges - pre_edges
    telemetry["boolean_changed_mesh"] = (
        telemetry["delta_faces"] != 0 or
        telemetry["delta_edges"] != 0 or
        (post_verts - pre_verts) != 0
    )
    telemetry["apply"] = apply_elapsed

    _debug_preserve_object_if_enabled(
        hole_obj,
        _format_debug_step_name("HOLE", "CUTTERS", "COMBINED"),
        kind="HOLE",
    )
    hole_mesh = hole_obj.data
    bpy.data.objects.remove(hole_obj, do_unlink=True)
    bpy.data.meshes.remove(hole_mesh)
    return telemetry

def build_osm_nodes(data):
    nodes = {}
    for element in data['elements']:
        if element['type'] == 'node':
            nodes[element['id']] = element
    return nodes



@log_workflow
def build_coloring_layer(map,kind = "WATER"):

    col_KeepManifold = (bpy.context.scene.tp3d.col_KeepManifold)
    if kind == "WATER":
        col_Area = (bpy.context.scene.tp3d.col_wArea)
    if kind == "FOREST":
        col_Area = (bpy.context.scene.tp3d.col_fArea)
    if kind == "CITY":
        col_Area = (bpy.context.scene.tp3d.col_cArea)
    if kind == "GLACIER":
        col_Area = (bpy.context.scene.tp3d.col_glArea)
    
    col_PaintMap = (bpy.context.scene.tp3d.col_PaintMap)
    process_islands = bool(getattr(bpy.context.scene.tp3d, "col_ProcessIslands", True))
    should_process_water_islands = (kind == "WATER" and process_islands)
    min_area_effective = _compute_effective_min_area(kind, col_Area)

    global exportformat
    if col_PaintMap == True:
        exportformat = "OBJ"

    bpy.context.preferences.edit.use_global_undo = False

    #print(f"ADDING {kind} MESH")
    #print(f"Map name: {map.name}")

    name = map.name

    waterDeleted = 0
    waterCreated = 0
    created_objects = []
    island_objects_to_paint = []
    global_bbox = (minLat, minLon, maxLat, maxLon)
    tile_lat, tile_lon = derive_osm_tile_size_from_scale(global_bbox, num_subdivisions, scaleHor if scaleHor else 1.0)
    probe = _probe_osm_payload(global_bbox, kind)
    max_elements = 35000
    max_bytes_estimate = 12 * 1024 * 1024
    max_polygons = 4000
    max_requests = bpy.context.scene.tp3d.col_glMaxRequests if kind == "GLACIER" else 40
    max_cumulative_bytes = 40 * 1024 * 1024
    cumulative_bytes = 0
    request_count = 0
    seen_way_ids = set()
    seen_relation_ids = set()
    relation_member_way_ids = set()
    render_standalone_ways_only = True  # Debug fallback: keep standalone way rendering while suppressing relation-member duplicates.
    relation_member_ways_skipped = 0
    relation_debug_pairs = []
    standalone_ways_rendered = 0

    if probe.get("ok"):
        module_logger.info("OSM probe kind=%s bbox=%s elements=%s estimated_bytes=%s", kind, global_bbox, probe["element_count"], probe["estimated_bytes"])
    else:
        module_logger.warning("OSM probe failed kind=%s bbox=%s", kind, global_bbox)

    use_single = probe.get("ok") and probe["element_count"] <= max_elements and probe["estimated_bytes"] <= max_bytes_estimate and probe["element_count"] <= max_polygons
    bboxes = [global_bbox] if use_single else _subdivide_bbox_grid(global_bbox, tile_lat, tile_lon)

    for idx, bbox in enumerate(bboxes, 1):
                if request_count >= max_requests or cumulative_bytes >= max_cumulative_bytes:
                    warn = f"OSM request budget exceeded for {kind}. Processed {request_count} tiles. Try smaller region."
                    module_logger.warning(warn)
                    show_message_box(warn, "WARNING", "WARNING")
                    break

                started = time.perf_counter()
                retries = 0
                try:
                    resp = fetch_osm_data(bbox, kind)
                    request_count += 1
                    retries = 0 if resp.get("ok") else 1
                    cumulative_bytes += int(resp.get("payload_size_bytes") or 0)
                    if not resp or not resp.get("ok"):
                        module_logger.warning(
                            "Skipping bbox=%s kind=%s due to OSM fetch failure status=%s error=%s endpoint=%s",
                            bbox,
                            kind,
                            resp.get("status_code") if isinstance(resp, dict) else None,
                            resp.get("error_type") if isinstance(resp, dict) else "unknown",
                            resp.get("endpoint") if isinstance(resp, dict) else None,
                        )
                        continue
                except Exception:
                    module_logger.exception("Unexpected error while fetching OSM data for bbox=%s kind=%s", bbox, kind)
                    show_message_box("Something went wrong with fetching OSM data, Try again maybe or idk")
                    continue

                data = resp.get("json_data") or {}
                if not isinstance(data, dict) or "elements" not in data:
                    module_logger.warning("OSM response missing elements for bbox=%s kind=%s", bbox, kind)
                    continue
                filtered_elements = []
                for el in data["elements"]:
                    if el.get("type") == "way":
                        if el["id"] in seen_way_ids:
                            continue
                        seen_way_ids.add(el["id"])
                    elif el.get("type") == "relation":
                        if el["id"] in seen_relation_ids:
                            continue
                        seen_relation_ids.add(el["id"])
                        for member in el.get("members", []):
                            if member.get("type") == "way" and "ref" in member:
                                relation_member_way_ids.add(member["ref"])
                    filtered_elements.append(el)
                module_logger.info("OSM tile telemetry kind=%s tile=%s/%s bbox=%s count=%s elapsed=%.3fs retries=%s", kind, idx, len(bboxes), bbox, len(filtered_elements), time.perf_counter() - started, retries)
                if kind == "WATER":
                    waterway_way_count = 0
                    water_polygon_count = 0
                    for el in filtered_elements:
                        if el.get("type") != "way":
                            continue
                        tags = el.get("tags") or {}
                        if tags.get("waterway") in {"river", "stream", "canal"}:
                            waterway_way_count += 1
                        if tags.get("natural") == "water" or tags.get("water") == "lake":
                            water_polygon_count += 1
                    module_logger.info(
                        "OSM water feature telemetry tile=%s/%s bbox=%s waterway_ways=%s water_polygons=%s",
                        idx,
                        len(bboxes),
                        bbox,
                        waterway_way_count,
                        water_polygon_count,
                    )
                nodes = build_osm_nodes({"elements": filtered_elements})
                bodies = extract_multipolygon_bodies(filtered_elements, nodes)
                #print(f"Nodes: {len(nodes)}, Bodies: {len(bodies)}")

                for i, body in enumerate(bodies):
                    relation_id = body.get("relation_id")
                    outer_rings = body.get("outers", [])
                    inner_rings = body.get("inners", [])
                    outer_rejections_by_reason = {
                        "not_closed": 0,
                        "too_few_points": 0,
                        "self_intersecting": 0,
                        "area_below_threshold": 0,
                    }
                    multipolygon_outer_area_threshold = min_area_effective

                    valid_outers = []
                    outer_rejections_by_reason = {
                        "empty": 0,
                        "not_closed": 0,
                        "too_few_points": 0,
                        "self_intersecting": 0,
                        "area_below_threshold": 0,
                    }
                    for outer_idx, ring in enumerate(outer_rings):
                        blender_ring = [convert_to_blender_coordinates(lat, lon, ele, 0) for lat, lon, ele in ring]
                        is_valid_outer, rejection_reason = classify_ring_validity(blender_ring, multipolygon_outer_area_threshold)
                        if is_valid_outer:
                            valid_outers.append(blender_ring)
                        else:
                            outer_rejections_by_reason[rejection_reason] = outer_rejections_by_reason.get(rejection_reason, 0) + 1
                            waterDeleted += 1
                            module_logger.info(
                                "Outer ring rejected relation=%s kind=%s outer_idx=%s reason=%s ring_points=%s area=%.8f threshold=%.8f",
                                relation_id,
                                kind,
                                outer_idx,
                                rejection_reason,
                                len(blender_ring),
                                calculate_polygon_area_2d(blender_ring),
                                multipolygon_outer_area_threshold,
                            )
                            if rejection_reason == "self_intersecting":
                                module_logger.warning(
                                    "Non-simple outer ring relation=%s kind=%s outer_idx=%s point_count=%s bbox=%s",
                                    relation_id,
                                    kind,
                                    outer_idx,
                                    len(blender_ring),
                                    _ring_bbox_2d(blender_ring),
                                )

                    valid_inners = []
                    inner_rejections_by_reason = {
                        "empty": 0,
                        "not_closed": 0,
                        "too_few_points": 0,
                        "self_intersecting": 0,
                        "area_below_threshold": 0,
                    }
                    inner_area_threshold = min_area_effective
                    module_logger.info(
                        "Multipolygon relation settings relation=%s kind=%s process_inner_holes=%s create_island_objects=%s inner_area_threshold=%.8f",
                        relation_id,
                        kind,
                        True,
                        should_process_water_islands,
                        inner_area_threshold,
                    )
                    for inner_idx, ring in enumerate(inner_rings):
                        blender_ring = [convert_to_blender_coordinates(lat, lon, ele, 0) for lat, lon, ele in ring]
                        is_valid_inner, rejection_reason = classify_ring_validity(blender_ring, inner_area_threshold)
                        if is_valid_inner:
                            valid_inners.append(blender_ring)
                        else:
                            inner_rejections_by_reason[rejection_reason] = inner_rejections_by_reason.get(rejection_reason, 0) + 1
                            module_logger.info(
                                "Inner ring rejected relation=%s kind=%s inner_idx=%s reason=%s ring_points=%s area=%.8f threshold=%.8f",
                                relation_id,
                                kind,
                                inner_idx,
                                rejection_reason,
                                len(blender_ring),
                                calculate_polygon_area_2d(blender_ring),
                                inner_area_threshold,
                            )
                    for outer_idx, outer_coords in enumerate(valid_outers):
                        outer_bbox = _ring_bbox_2d(outer_coords)
                        outer_area = calculate_polygon_area_2d(outer_coords)
                        module_logger.info(
                            "Outer ring geometry relation=%s kind=%s outer_idx=%s ring_points=%s area=%.8f bbox=%s",
                            relation_id,
                            kind,
                            outer_idx,
                            len(outer_coords),
                            outer_area,
                            outer_bbox,
                        )

                    holes_applied_total = 0
                    island_objects_created = 0
                    island_objects_failed = 0

                    # Explicitly create visible island meshes from valid inner rings so islands remain
                    # present even when hole visibility is affected by viewport/render filtering.
                    island_objects = []
                    if should_process_water_islands:
                        for inner_idx, inner_coords in enumerate(valid_inners):
                            island_obj = col_create_face_mesh(f"Island_{relation_id}_{i}_{inner_idx}", inner_coords)
                            if not island_obj:
                                island_objects_failed += 1
                                continue
                            island_obj.hide_set(False)
                            island_obj.hide_viewport = False
                            island_obj.hide_render = False
                            writeMetadata(island_obj, "MAP")
                            island_mat = bpy.data.materials.get("MAP") or bpy.data.materials.get("CITY") or bpy.data.materials.get("FOREST")
                            if island_mat:
                                island_obj.data.materials.clear()
                                island_obj.data.materials.append(island_mat)
                            island_objects.append(island_obj)
                            island_objects_to_paint.append(island_obj)
                            relation_debug_pairs.append((relation_id, island_obj.name, None))
                            island_objects_created += 1

                    for j, outer_coords in enumerate(valid_outers):
                        assigned_inners = []
                        for inner_idx, inner_coords in enumerate(valid_inners):
                            inner_bbox = _ring_bbox_2d(inner_coords)
                            inner_area = calculate_polygon_area_2d(inner_coords)
                            inner_centroid = _ring_centroid_2d(inner_coords)
                            contained = _point_in_ring_2d(inner_centroid, outer_coords) if inner_centroid else False
                            module_logger.info(
                                "Inner assignment relation=%s kind=%s outer_idx=%s inner_idx=%s ring_points=%s area=%.8f centroid=%s bbox=%s contained=%s assigned_to_outer_idx=%s",
                                relation_id,
                                kind,
                                j,
                                inner_idx,
                                len(inner_coords),
                                inner_area,
                                inner_centroid,
                                inner_bbox,
                                contained,
                                j if contained else None,
                            )
                            if contained:
                                assigned_inners.append(inner_coords)
                            else:
                                module_logger.warning(
                                    "Inner ring skipped due to containment mismatch relation=%s kind=%s outer_idx=%s inner_idx=%s centroid=%s outer_bbox=%s inner_bbox=%s",
                                    relation_id,
                                    kind,
                                    j,
                                    inner_idx,
                                    inner_centroid,
                                    _ring_bbox_2d(outer_coords),
                                    inner_bbox,
                                )

                        relation_quality_log = {
                            "pre_clean_stats": _mesh_health_stats(None),
                            "post_clean_stats": _mesh_health_stats(None),
                            "cleaning_actions": [],
                            "quality_gate_passed": False,
                        }

                        outer_obj = col_create_face_mesh(f"Relation_{relation_id}_{i}_{j}_outer", outer_coords)
                        if not outer_obj:
                            waterDeleted += 1
                            module_logger.warning("Outer water mesh build failed before hole carving relation=%s kind=%s outer_idx=%s reason=outer_creation_failed", relation_id, kind, j)
                            continue

                        relation_quality_log["pre_clean_stats"] = _mesh_health_stats(outer_obj)
                        relation_quality_log["cleaning_actions"] = _sanitize_water_outer_mesh(outer_obj)
                        relation_quality_log["post_clean_stats"] = _mesh_health_stats(outer_obj)

                        non_manifold_threshold = int(getattr(bpy.context.scene.tp3d, "col_WaterMeshNonManifoldEdgeThreshold", 0))
                        post_stats = relation_quality_log["post_clean_stats"]
                        quality_gate_passed = (
                            post_stats.get("zero_area_faces", 0) == 0 and
                            post_stats.get("loose_edges", 0) == 0 and
                            post_stats.get("non_manifold_edges", 0) <= non_manifold_threshold
                        )
                        relation_quality_log["quality_gate_passed"] = quality_gate_passed

                        if quality_gate_passed:
                            tobj, hole_telemetry = col_create_face_mesh_with_holes(
                                f"Relation_{relation_id}_{i}_{j}",
                                outer_coords,
                                assigned_inners,
                                relation_id=relation_id,
                                outer_idx=j,
                            )
                            bpy.data.objects.remove(outer_obj, do_unlink=True)
                            if not tobj:
                                waterDeleted += 1
                                module_logger.warning("Hole carving failed after quality pass relation=%s kind=%s outer_idx=%s reason=hole_mesh_creation_failed quality_log=%s", relation_id, kind, j, relation_quality_log)
                                continue
                        else:
                            gate_reason = f"quality_gate_failed(non_manifold={post_stats.get('non_manifold_edges', 0)}/{non_manifold_threshold}, zero_area={post_stats.get('zero_area_faces', 0)}, loose_edges={post_stats.get('loose_edges', 0)})"
                            module_logger.warning("Skipping hole carving and falling back to sanitized outer mesh relation=%s kind=%s outer_idx=%s reason=%s quality_log=%s", relation_id, kind, j, gate_reason, relation_quality_log)
                            tobj = outer_obj
                            hole_telemetry = {
                                "candidate_holes": len(assigned_inners or []),
                                "holes_applied": 0,
                                "boolean_changed_mesh": False,
                                "delta_faces": 0,
                                "delta_edges": 0,
                                "prep": 0.0,
                                "apply": 0.0,
                                "source": "fallback_outer_mesh_quality_gate_failed",
                            }

                        pre_health = relation_quality_log["post_clean_stats"]
                        holes_applied_total += hole_telemetry["holes_applied"]
                        module_logger.info(
                            "Hole non-boolean telemetry relation=%s outer_idx=%s kind=%s source=%s prep=%.4fs apply=%.4fs candidate_holes=%s holes_applied=%s mesh_changed=%s delta_faces=%s delta_edges=%s",
                            relation_id,
                            j,
                            kind,
                            hole_telemetry.get("source"),
                            hole_telemetry["prep"],
                            hole_telemetry["apply"],
                            hole_telemetry["candidate_holes"],
                            hole_telemetry["holes_applied"],
                            hole_telemetry["boolean_changed_mesh"],
                            hole_telemetry["delta_faces"],
                            hole_telemetry["delta_edges"],
                        )
                        post_health = _mesh_health_stats(tobj)
                        module_logger.info(
                            "Hole non-boolean mesh health relation=%s outer_idx=%s kind=%s pre=%s post=%s",
                            relation_id,
                            j,
                            kind,
                            pre_health,
                            post_health,
                        )
                        module_logger.info(
                            "Hole relation quality relation=%s outer_idx=%s kind=%s quality=%s",
                            relation_id,
                            j,
                            kind,
                            relation_quality_log,
                        )
                        if hole_telemetry["holes_applied"] == 0 and valid_inners:
                            module_logger.warning(
                                "Hole non-boolean yielded zero holes despite valid inner rings relation=%s kind=%s outer_idx=%s valid_inners=%s",
                                relation_id,
                                kind,
                                j,
                                len(valid_inners),
                            )
                        if hole_telemetry["holes_applied"] > 0 and not hole_telemetry["boolean_changed_mesh"]:
                            module_logger.warning(
                                "Hole non-boolean generated holes but mesh_changed flag is false relation=%s kind=%s outer_idx=%s holes_applied=%s candidate_holes=%s",
                                relation_id,
                                kind,
                                j,
                                hole_telemetry["holes_applied"],
                                hole_telemetry["candidate_holes"],
                            )
                        created_objects.append(tobj)
                        if should_process_water_islands:
                            for island_obj in island_objects:
                                relation_debug_pairs.append((
                                    relation_id,
                                    island_obj.name if island_obj else None,
                                    tobj.name if tobj else None,
                                ))
                        waterCreated += 1

                    if holes_applied_total > 0 and island_objects_created == 0:
                        module_logger.warning(
                            "Holes were applied but no island objects were created relation=%s kind=%s holes_applied=%s valid_inners=%s",
                            relation_id,
                            kind,
                            holes_applied_total,
                            len(valid_inners),
                        )

                    module_logger.info(
                        "Multipolygon relation=%s kind=%s outer_rings=%s inner_rings=%s valid_outers=%s valid_inners=%s holes_applied=%s island_objects_created=%s island_objects_failed=%s outer_rejections_by_reason=%s inner_rejections_by_reason=%s inner_area_threshold=%.8f",
                        relation_id,
                        kind,
                        len(outer_rings),
                        len(inner_rings),
                        len(valid_outers),
                        len(valid_inners),
                        holes_applied_total,
                        island_objects_created,
                        island_objects_failed,
                        outer_rejections_by_reason,
                        inner_rejections_by_reason,
                        inner_area_threshold,
                    )

                for i, element in enumerate(filtered_elements):
                    #print(i)
                    if element['type'] != 'way':
                        waterDeleted += 1
                        continue
                    if element.get("id") in relation_member_way_ids:
                        relation_member_ways_skipped += 1
                        continue
                    if not render_standalone_ways_only:
                        continue

                    coords = []
                    for node_id in element.get('nodes', []):
                        if node_id in nodes:
                            node = nodes[node_id]
                            coord = convert_to_blender_coordinates(
                                node['lat'], node['lon'], 0,0
                            )
                            coords.append(coord)
                    tArea = calculate_polygon_area_2d(coords)
                    #print(f"tArea2: {tArea}")
                    is_closed_way = len(coords) >= 3 and coords[0] == coords[-1]
                    if len(coords) < 2:
                        waterDeleted += 1
                        continue
                    if is_closed_way and tArea < min_area_effective:
                        waterDeleted += 1
                        continue
                    
                    tags = element.get("tags", {})
                    if is_closed_way:
                        tobj = col_create_face_mesh(f"coloredObject_{i}", coords)
                        created_objects.append(tobj)
                        waterCreated += 1
                        standalone_ways_rendered += 1
                    else:
                        tobj = col_create_line_mesh(f"OpenObject_{i}", coords)
                        created_objects.append(tobj)
                        waterCreated += 1
                        standalone_ways_rendered += 1
                    
                time.sleep(1)  # Pause to prevent request throttling
            
    # --- Merge all created water meshes into one ---

    print(f"{kind} Objects Created: {waterCreated}, Objects Ignored: {waterDeleted}")
    module_logger.info(
        "Duplicate fill telemetry kind=%s relation_member_ways_skipped=%s standalone_ways_rendered=%s relation_member_way_ids=%s",
        kind,
        relation_member_ways_skipped,
        standalone_ways_rendered,
        len(relation_member_way_ids),
    )

    #print(f"Creating {kind} Objects")
    if created_objects:
        ctx = bpy.context
        bpy.ops.object.select_all(action='DESELECT')
        found = 0
        biggestArea = 0
        kept_objects = []
        for tobj in created_objects:
            if not _is_valid_blender_object(tobj):
                continue
            
            bm = bmesh.new()
            bm.from_mesh(tobj.data)
            area = sum(f.calc_area() for f in bm.faces)
            bm.free()
            #print(f"Area: {area}")
            if area > biggestArea:
                biggestArea = area
            if area >= min_area_effective:
                found = 1
                tobj.select_set(True)
                ctx.view_layer.objects.active = tobj
                kept_objects.append(tobj)
                #print(f"Area: {area}")
            else:
                mesh_data = tobj.data
                _debug_preserve_object_if_enabled(
                    tobj,
                    _format_debug_step_name("WATER", "AREA_FILTERED", "FRAGMENT"),
                    kind="WATER",
                )
                bpy.data.objects.remove(tobj, do_unlink=True)
                bpy.data.meshes.remove(mesh_data)
                #print("Removed")

            if found == 0:
                continue
        
        created_objects = kept_objects
        dropped_fragment_count = 0
        smallest_kept_area = None
        if kind == "WATER":
            for tobj in created_objects:
                if _is_valid_blender_object(tobj):
                    dropped, smallest = _remove_small_mesh_islands(tobj, min_area_effective)
                    dropped_fragment_count += dropped
                    if smallest is not None:
                        smallest_kept_area = smallest if smallest_kept_area is None else min(smallest_kept_area, smallest)
            module_logger.info(
                "WATER area gate debug kind=%s min_area_effective=%.8f dropped_fragment_count=%s smallest_kept_area=%s",
                kind,
                min_area_effective,
                dropped_fragment_count,
                f"{smallest_kept_area:.8f}" if smallest_kept_area is not None else "None",
            )

        print(f"Biggest {kind} Found has a Area of: {biggestArea}")

        if biggestArea == 0:
            print("No Water Found on Tile")
            return
        
        bpy.ops.object.join()  # This merges them into the active object
        
        merged_object = ctx.view_layer.objects.active
        bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')


        #SETUP FOR MODIFIERS
        
        bpy.context.view_layer.objects.active = merged_object
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.mesh.select_all(action='SELECT')
        bpy.ops.mesh.extrude_region_move()
        bpy.ops.transform.translate(value=(0, 0, 200))#bpy.ops.mesh.select_all(action='DESELECT')
        bpy.ops.object.mode_set(mode='OBJECT')
        merged_object.location.z -= 1


        #Add Decimate modifier
        #dec_mod = merged_object.modifiers.new(name="Decimate", type="DECIMATE")
        #dec_mod.decimate_type = "UNSUBDIV"
        #dec_mod.iterations = 1

        #bpy.ops.object.modifier_apply(modifier=dec_mod.name)

        recalculateNormals(merged_object)


        # Add boolean modifier
        bool_mod = merged_object.modifiers.new(name="Boolean", type='BOOLEAN')
        bool_mod.object = map
        bool_mod.operation = 'INTERSECT'
        bool_mod.solver = 'MANIFOLD'


        #appla boolean modifier
        bpy.ops.object.modifier_apply(modifier=bool_mod.name)


        bpy.ops.object.mode_set(mode="EDIT")
        bm = bmesh.from_edit_mesh(merged_object.data)

        bm.verts.ensure_lookup_table()
        bm.faces.ensure_lookup_table()


        #Get lowest Vertice
        try:
            min_z = min(v.co.z for v in bm.verts)
        #IF NO VERTICES ARE LEFT, END FUNCTION
        except:
            bpy.ops.object.mode_set(mode='OBJECT')
            return
        
        tol = 0.1

        lowestVert = 100
        for v in bm.verts:
            if abs(v.co.z - min_z) < tol:
                v.select = True
            else:
                v.select = False
                if v.co.z < lowestVert:
                    lowestVert = v.co.z
        
        bpy.context.tool_settings.mesh_select_mode = (True, False, False)
        bmesh.ops.delete(bm, geom=[elem for elem in bm.verts[:] + bm.edges[:] + bm.faces[:] if elem.select], context='VERTS')
    

        bpy.ops.mesh.select_all(action='SELECT')
        bpy.ops.mesh.extrude_region_move()
        bpy.ops.transform.translate(value=(0, 0, -1))#bpy.ops.mesh.select_all(action='DESELECT')


        bmesh.update_edit_mesh(merged_object.data)
        bpy.ops.object.mode_set(mode="OBJECT")

        #recalculate normals again after the Boolean operation
        recalculateNormals(merged_object)

        #Disabled for now
        if col_KeepManifold == 0 and 1 == 0:
            delete_non_manifold(merged_object)

        #merged_object.location.z += 0.05
        merged_object.name = name + "_" + kind

        bpy.context.view_layer.objects.active = merged_object
        merged_object.select_set(True)


        meshm = merged_object.data
        for i, vert in enumerate(meshm.vertices):
            vert.co.z -= 0.9
        merged_object.location.z = 0

        #bpy.ops.object.transform_apply(location=True, rotation=False, scale=False)
        
        if kind == "WATER" and _is_valid_blender_object(merged_object):
            post_merge_dropped, post_merge_smallest = _remove_small_mesh_islands(merged_object, min_area_effective)
            module_logger.info(
                "WATER post-merge area gate kind=%s min_area_effective=%.8f dropped_fragment_count=%s smallest_kept_area=%s",
                kind,
                min_area_effective,
                post_merge_dropped,
                f"{post_merge_smallest:.8f}" if post_merge_smallest is not None else "None",
            )
            if len(merged_object.data.polygons) == 0:
                module_logger.warning(
                    "WATER post-merge cleanup removed all polygons object=%s min_area_effective=%.8f",
                    merged_object.name,
                    min_area_effective,
                )
                mesh_data = merged_object.data
                _debug_preserve_object_if_enabled(
                    merged_object,
                    _format_debug_step_name("WATER", "POST_BOOLEAN", "MERGED"),
                    kind="WATER",
                )
                bpy.data.objects.remove(merged_object, do_unlink=True)
                bpy.data.meshes.remove(mesh_data)
                return
            recalculateNormals(merged_object)

        if merged_object:
            #print(f"Merged obj: {merged_object}, Kind: {kind}")
            writeMetadata(merged_object,kind)
            mat = bpy.data.materials.get(kind)
            merged_object.data.materials.clear()
            merged_object.data.materials.append(mat)
            recalculateNormals(merged_object)
            module_logger.info(
                "Post-boolean water normals refreshed object=%s kind=%s material_slots=%s",
                merged_object.name,
                kind,
                [m.name for m in merged_object.data.materials],
            )
        
        if col_PaintMap == False:
            export_to_STL(merged_object)


    if should_process_water_islands:
        for relation_id, land_obj_name, water_obj_name in relation_debug_pairs:
            land_obj = bpy.data.objects.get(land_obj_name) if land_obj_name else None
            if water_obj_name:
                water_obj = bpy.data.objects.get(water_obj_name)
            else:
                water_obj = merged_object if "merged_object" in locals() else None
            _apply_deterministic_z_offset(land_obj, water_obj, relation_id, land_offset=0.0005, water_offset=0.0)

    for area in bpy.context.screen.areas:
        if area.type == 'VIEW_3D':  # make sure it's a 3D Viewport
            for space in area.spaces:
                if space.type == 'VIEW_3D':
                    space.shading.type = 'MATERIAL'  # switch shading

                
    bpy.context.preferences.edit.use_global_undo = True

    merged_ref = merged_object if "merged_object" in locals() else None
    return {
        "kind": kind,
        "merged_object": merged_ref,
        "island_objects": list(island_objects_to_paint),
        "cleanup_telemetry": {
            "objects_created": waterCreated,
            "objects_ignored": waterDeleted,
            "relation_member_ways_skipped": relation_member_ways_skipped,
            "standalone_ways_rendered": standalone_ways_rendered,
            "relation_member_way_ids": len(relation_member_way_ids),
        },
    }


def paint_coloring_layer(map_obj, layer_artifact):
    if not layer_artifact:
        return None

    kind = layer_artifact.get("kind")
    merged_object = layer_artifact.get("merged_object")
    island_objects = layer_artifact.get("island_objects") or []
    col_PaintMap = bpy.context.scene.tp3d.col_PaintMap

    if col_PaintMap and _is_valid_blender_object(merged_object):
        color_map_faces_by_terrain(map_obj, merged_object)
        if kind == "WATER" and bpy.context.scene.tp3d.col_WaterSpotCleanup:
            _debug_preserve_object_if_enabled(
                map_obj,
                _format_debug_step_name("WATER", "PRE_SPOT_CLEANUP_MAP"),
                kind="WATER",
            )
            _cleanup_water_paint_clusters(
                map_obj,
                water_material_name="WATER",
                base_material_name="BASE",
                tiny_cluster_mul=bpy.context.scene.tp3d.col_WaterSpotCleanupMul,
                hole_fill_enabled=bpy.context.scene.tp3d.col_WaterHoleFillEnabled,
                hole_fill_mul=bpy.context.scene.tp3d.col_WaterHoleFillMul,
            )
            _debug_preserve_object_if_enabled(
                map_obj,
                _format_debug_step_name("WATER", "POST_SPOT_CLEANUP_MAP"),
                kind="WATER",
            )
        mesh_data = merged_object.data
        _debug_preserve_object_if_enabled(
            merged_object,
            _format_debug_step_name("WATER", "POST_PAINT", "CLEANUP"),
            kind="WATER",
        )
        bpy.data.objects.remove(merged_object, do_unlink=True)
        bpy.data.meshes.remove(mesh_data)
        layer_artifact["merged_object"] = None

    return layer_artifact.get("merged_object")


def coloring_main(map,kind = "WATER"):
    layer_artifact = build_coloring_layer(map, kind)
    paint_coloring_layer(map, layer_artifact)
    return layer_artifact.get("merged_object")

def paint_islands_on_map(map_obj, island_objects):
    map_name = map_obj.name if map_obj else None
    counters = {
        "islands_total": len(island_objects or []),
        "islands_valid_mesh": 0,
        "islands_invalid": 0,
        "islands_with_zero_polys": 0,
        "islands_painted_success": 0,
        "islands_painted_zero_faces": 0,
    }

    if not island_objects:
        module_logger.info("Island paint pass skipped: no pending islands for map=%s", map_name)
        module_logger.info("Island paint summary | map=%s %s", map_name, counters)
        return

    for island_obj in island_objects:
        if _is_valid_blender_object(island_obj) and island_obj.type == 'MESH':
            counters["islands_valid_mesh"] += 1
            polygon_count = len(island_obj.data.polygons) if island_obj.data else 0
            if polygon_count == 0:
                counters["islands_with_zero_polys"] += 1

            island_min_z, island_max_z = _mesh_z_range(island_obj)
            map_min_z, map_max_z = _mesh_z_range(map_obj)
            island_mat_names = [m.name for m in island_obj.data.materials] if island_obj.data else []
            map_mat_names = [m.name for m in map_obj.data.materials] if map_obj and map_obj.data else []
            module_logger.info(
                "Island final paint debug: map=%s island=%s island_obj_type=%s island_verts=%s island_polys=%s island_z_range=(%s,%s) map_z_range=(%s,%s) island_loc=(%.6f,%.6f,%.6f) map_loc=(%.6f,%.6f,%.6f) island_mats=%s map_mats=%s",
                map_name,
                island_obj.name,
                island_obj.get("Object type") if "Object type" in island_obj else None,
                len(island_obj.data.vertices) if island_obj.data else 0,
                polygon_count,
                island_min_z,
                island_max_z,
                map_min_z,
                map_max_z,
                island_obj.location.x,
                island_obj.location.y,
                island_obj.location.z,
                map_obj.location.x if map_obj else 0.0,
                map_obj.location.y if map_obj else 0.0,
                map_obj.location.z if map_obj else 0.0,
                island_mat_names,
                map_mat_names,
            )
            island_metrics = color_map_faces_by_terrain(map_obj, island_obj, paint_material_name="BASE", return_metrics=True) or {}
            faces_colored = int(island_metrics.get("faces_colored", 0) or 0)
            faces_checked_up = int(island_metrics.get("faces_checked_up", 0) or 0)
            ray_hits = int(island_metrics.get("ray_hits", 0) or 0)
            hit_rate = (ray_hits / faces_checked_up) if faces_checked_up > 0 else 0.0
            if faces_colored > 0:
                counters["islands_painted_success"] += 1
            else:
                counters["islands_painted_zero_faces"] += 1

            module_logger.info(
                "Island paint metrics | map=%s island=%s polygon_count=%s faces_colored=%s hit_rate=%.4f faces_checked_up=%s ray_hits=%s material_name_used=%s",
                map_name,
                island_obj.name,
                polygon_count,
                faces_colored,
                hit_rate,
                faces_checked_up,
                ray_hits,
                island_metrics.get("material_name_used"),
            )
            if faces_colored == 0 and polygon_count > 0:
                module_logger.warning(
                    "Island paint zero-face warning | map=%s island=%s polygon_count=%s faces_colored=%s hit_rate=%.4f",
                    map_name,
                    island_obj.name,
                    polygon_count,
                    faces_colored,
                    hit_rate,
                )

            mesh_data = island_obj.data
            _debug_preserve_object_if_enabled(
                island_obj,
                _format_debug_step_name("WATER", "ISLAND_PAINT", "SOURCE"),
                kind="WATER",
            )
            bpy.data.objects.remove(island_obj, do_unlink=True)
            bpy.data.meshes.remove(mesh_data)
        else:
            counters["islands_invalid"] += 1
            module_logger.warning(
                "Island final paint skipped invalid island object: island=%s valid=%s type=%s",
                getattr(island_obj, "name", None),
                _is_valid_blender_object(island_obj),
                getattr(island_obj, "type", None),
            )

    module_logger.info("Island paint summary | map=%s %s", map_name, counters)
    


def _is_valid_blender_object(obj):
    if obj is None:
        return False
    try:
        _ = obj.name
        _ = obj.type
        return True
    except ReferenceError:
        return False


def _mesh_z_range(obj):
    if not _is_valid_blender_object(obj) or obj.type != 'MESH' or not obj.data.vertices:
        return None, None
    zs = [v.co.z for v in obj.data.vertices]
    return min(zs), max(zs)


def _apply_deterministic_z_offset(land_obj, water_obj, relation_id, land_offset=0.0005, water_offset=0.0):
    """Apply stable z-offsets so land/water are not coplanar after booleans."""
    def _safe_obj_name(obj):
        return obj.name if _is_valid_blender_object(obj) else None

    if _is_valid_blender_object(land_obj) and land_obj.type == 'MESH':
        for v in land_obj.data.vertices:
            v.co.z += land_offset
        land_obj.data.update()
    if _is_valid_blender_object(water_obj) and water_obj.type == 'MESH' and water_offset != 0.0:
        for v in water_obj.data.vertices:
            v.co.z += water_offset
        water_obj.data.update()

    land_min, land_max = _mesh_z_range(land_obj)
    water_min, water_max = _mesh_z_range(water_obj)
    coplanar = (
        land_min is not None and water_min is not None and
        abs(land_min - water_min) < 1e-7 and abs(land_max - water_max) < 1e-7
    )
    module_logger.info(
        "Relation final z-range relation=%s land_obj=%s water_obj=%s land_range=(%s,%s) water_range=(%s,%s) coplanar=%s land_offset=%.7f water_offset=%.7f land_mats=%s water_mats=%s",
        relation_id,
        _safe_obj_name(land_obj),
        _safe_obj_name(water_obj),
        land_min,
        land_max,
        water_min,
        water_max,
        coplanar,
        land_offset,
        water_offset,
        [m.name for m in land_obj.data.materials] if _is_valid_blender_object(land_obj) and land_obj.type == 'MESH' else [],
        [m.name for m in water_obj.data.materials] if _is_valid_blender_object(water_obj) and water_obj.type == 'MESH' else [],
    )



def _face_clusters_by_material(bm, material_index):
    visited = set()
    clusters = []
    for face in bm.faces:
        if face.index in visited or face.material_index != material_index:
            continue
        stack = [face]
        visited.add(face.index)
        cluster_faces = []
        area = 0.0
        while stack:
            current = stack.pop()
            cluster_faces.append(current)
            area += current.calc_area()
            for edge in current.edges:
                for other in edge.link_faces:
                    if other.index not in visited and other.material_index == material_index:
                        visited.add(other.index)
                        stack.append(other)
        clusters.append((cluster_faces, area))
    return clusters




def _cluster_shape_metrics(cluster_faces, material_index):
    cluster_face_set = set(cluster_faces)
    area = 0.0
    boundary_length = 0.0
    boundary_edges = 0
    for f in cluster_faces:
        face_area = f.calc_area()
        area += face_area
        for e in f.edges:
            linked_same_cluster = any(lf in cluster_face_set for lf in e.link_faces if lf != f)
            if not linked_same_cluster:
                boundary_edges += 1
                boundary_length += e.calc_length()

    perimeter_area_ratio = (boundary_length / area) if area > 1e-12 else float('inf')
    compactness = (4.0 * math.pi * area / (boundary_length * boundary_length)) if boundary_length > 1e-12 else 0.0
    return {
        "face_count": len(cluster_faces),
        "area": area,
        "boundary_length": boundary_length,
        "boundary_edges": boundary_edges,
        "perimeter_area_ratio": perimeter_area_ratio,
        "compactness": compactness,
    }


def _extract_thin_bridge_faces(cluster_faces, area_scale):
    cluster_face_set = set(cluster_faces)
    bridge_faces = []
    for f in cluster_faces:
        internal_neighbors = 0
        boundary_edges = 0
        for e in f.edges:
            has_internal = False
            for lf in e.link_faces:
                if lf != f and lf in cluster_face_set:
                    has_internal = True
                    internal_neighbors += 1
                    break
            if not has_internal:
                boundary_edges += 1

        if internal_neighbors <= 2 and boundary_edges >= max(2, len(f.edges) // 2):
            if f.calc_area() <= area_scale:
                bridge_faces.append(f)
    return bridge_faces


def _material_face_histogram(bm, mesh):
    histogram = {}
    for face in bm.faces:
        mat_index = face.material_index
        mat_name = None
        if 0 <= mat_index < len(mesh.materials):
            mat_slot = mesh.materials[mat_index]
            mat_name = mat_slot.name if mat_slot else "<None>"
        if not mat_name:
            mat_name = "<UNASSIGNED>"
        key = (mat_index, mat_name)
        histogram[key] = histogram.get(key, 0) + 1
    return histogram


def _format_material_face_histogram(histogram):
    if not histogram:
        return "none"
    ordered_items = sorted(histogram.items(), key=lambda item: (-item[1], item[0][0], item[0][1]))
    return ", ".join(f"{mat_index}:{mat_name}={count}" for (mat_index, mat_name), count in ordered_items)
def _cleanup_water_paint_clusters(map_obj, water_material_name="WATER", base_material_name="BASE", tiny_cluster_mul=2.0, hole_fill_enabled=False, hole_fill_mul=1.0, hole_fill_min_faces=2):
    if not _is_valid_blender_object(map_obj) or map_obj.type != 'MESH':
        return

    mesh = map_obj.data
    water_index = mesh.materials.find(water_material_name)
    base_index = mesh.materials.find(base_material_name)
    if water_index < 0 or base_index < 0:
        module_logger.info("WATER spot cleanup skipped map=%s water_index=%s base_index=%s", map_obj.name, water_index, base_index)
        return

    bm = bmesh.new()
    bm.from_mesh(mesh)
    bm.faces.ensure_lookup_table()
    hist_before = _material_face_histogram(bm, mesh)

    map_face_areas = sorted(f.calc_area() for f in bm.faces if f.calc_area() > 0)
    median_face_area = map_face_areas[len(map_face_areas)//2] if map_face_areas else 0.0
    tiny_cluster_threshold = median_face_area * max(0.0, tiny_cluster_mul)
    hole_fill_threshold = median_face_area * max(0.0, hole_fill_mul)

    water_clusters_before = _face_clusters_by_material(bm, water_index)
    water_areas_before = sorted((a for _, a in water_clusters_before), reverse=True)
    largest_before = water_areas_before[0] if water_areas_before else 0.0
    median_before = water_areas_before[len(water_areas_before)//2] if water_areas_before else 0.0
    smallest_before = water_areas_before[-1] if water_areas_before else 0.0
    removal_candidates = sorted((area for _, area in water_clusters_before if area < tiny_cluster_threshold))
    keep_candidates = sorted((area for _, area in water_clusters_before if area >= tiny_cluster_threshold))
    sample_limit = 20
    module_logger.info(
        "WATER spot cleanup candidates map=%s total_clusters=%s tiny_cluster_threshold=%.8f smallest_cluster_before=%.8f "
        "removal_candidate_count=%s keep_candidate_count=%s removal_candidate_areas_sample=%s keep_candidate_areas_sample=%s",
        map_obj.name,
        len(water_clusters_before),
        tiny_cluster_threshold,
        smallest_before,
        len(removal_candidates),
        len(keep_candidates),
        [round(v, 8) for v in removal_candidates[:sample_limit]],
        [round(v, 8) for v in keep_candidates[:sample_limit]],
    )

    bridge_face_threshold = median_face_area * 1.5 if median_face_area > 0.0 else 0.0
    thin_ratio_threshold = 12.0
    thin_compactness_threshold = 0.12
    thin_area_gate = tiny_cluster_threshold * 1.8 if tiny_cluster_threshold > 0.0 else 0.0

    removed_area = 0.0
    removed_clusters = 0
    flagged_thin_kept_clusters = 0
    bridge_faces_reclassified = 0
    for faces, area in water_clusters_before:
        metrics = _cluster_shape_metrics(faces, water_index)
        thin_topology = (
            metrics["area"] <= thin_area_gate and
            (
                metrics["perimeter_area_ratio"] >= thin_ratio_threshold or
                metrics["compactness"] <= thin_compactness_threshold
            )
        )

        if area < tiny_cluster_threshold:
            module_logger.debug(
                "WATER spot cleanup removing cluster map=%s cluster_area=%.8f threshold=%.8f face_count=%s boundary_len=%.8f pa_ratio=%.8f compactness=%.8f",
                map_obj.name,
                area,
                tiny_cluster_threshold,
                metrics["face_count"],
                metrics["boundary_length"],
                metrics["perimeter_area_ratio"],
                metrics["compactness"],
            )
            removed_clusters += 1
            removed_area += area
            for f in faces:
                f.material_index = base_index
            continue

        if thin_topology and bridge_face_threshold > 0.0:
            bridge_faces = _extract_thin_bridge_faces(faces, bridge_face_threshold)
            if bridge_faces:
                for bf in bridge_faces:
                    bf.material_index = base_index
                bridge_faces_reclassified += len(bridge_faces)
                flagged_thin_kept_clusters += 1
                module_logger.info(
                    "WATER thin-bridge artifact map=%s cluster_area=%.8f threshold=%.8f face_count=%s bridge_faces_reclassified=%s boundary_len=%.8f pa_ratio=%.8f compactness=%.8f",
                    map_obj.name,
                    area,
                    tiny_cluster_threshold,
                    metrics["face_count"],
                    len(bridge_faces),
                    metrics["boundary_length"],
                    metrics["perimeter_area_ratio"],
                    metrics["compactness"],
                )
            else:
                flagged_thin_kept_clusters += 1
                module_logger.info(
                    "WATER thin-bridge artifact kept for connectivity map=%s cluster_area=%.8f threshold=%.8f face_count=%s boundary_len=%.8f pa_ratio=%.8f compactness=%.8f",
                    map_obj.name,
                    area,
                    tiny_cluster_threshold,
                    metrics["face_count"],
                    metrics["boundary_length"],
                    metrics["perimeter_area_ratio"],
                    metrics["compactness"],
                )

    filled_holes = 0
    filled_area = 0.0
    base_clusters_considered = 0
    enclosed_clusters_promoted = 0
    promoted_area = 0.0
    if hole_fill_enabled and hole_fill_threshold > 0.0:
        base_clusters = _face_clusters_by_material(bm, base_index)
        for faces, area in base_clusters:
            if area >= hole_fill_threshold or len(faces) < hole_fill_min_faces:
                continue
            base_clusters_considered += 1
            cluster_face_set = set(faces)
            enclosed_by_water = True
            touches_mesh_boundary = False
            for f in faces:
                for e in f.edges:
                    link_faces = e.link_faces
                    if len(link_faces) == 1:
                        touches_mesh_boundary = True
                        enclosed_by_water = False
                        break
                    for lf in link_faces:
                        if lf not in cluster_face_set and lf.material_index != water_index:
                            enclosed_by_water = False
                            break
                    if not enclosed_by_water:
                        break
                if not enclosed_by_water:
                    break
            if enclosed_by_water and not touches_mesh_boundary:
                filled_holes += 1
                filled_area += area
                enclosed_clusters_promoted += 1
                promoted_area += area
                for f in faces:
                    f.material_index = water_index

    water_clusters_after = _face_clusters_by_material(bm, water_index)
    water_areas_after = sorted((a for _, a in water_clusters_after), reverse=True)
    largest_after = water_areas_after[0] if water_areas_after else 0.0
    median_after = water_areas_after[len(water_areas_after)//2] if water_areas_after else 0.0

    bm.to_mesh(mesh)
    bm.free()

    bm_hist_after = bmesh.new()
    bm_hist_after.from_mesh(mesh)
    bm_hist_after.faces.ensure_lookup_table()
    hist_after = _material_face_histogram(bm_hist_after, mesh)
    bm_hist_after.free()

    module_logger.info(
        "WATER spot cleanup map=%s median_face_area=%.8f tiny_cluster_threshold=%.8f hole_fill_enabled=%s hole_fill_threshold=%.8f hole_fill_min_faces=%s clusters_before=%s clusters_after=%s removed_clusters=%s removed_painted_area=%.8f filled_holes=%s filled_area=%.8f base_clusters_considered=%s enclosed_clusters_promoted=%s promoted_area=%.8f thin_kept_clusters=%s bridge_faces_reclassified=%s largest_cluster_before=%.8f median_cluster_before=%.8f largest_cluster_after=%.8f median_cluster_after=%.8f material_faces_before=[%s] material_faces_after=[%s]",
        map_obj.name,
        median_face_area,
        tiny_cluster_threshold,
        hole_fill_enabled,
        hole_fill_threshold,
        hole_fill_min_faces,
        len(water_clusters_before),
        len(water_clusters_after),
        removed_clusters,
        removed_area,
        filled_holes,
        filled_area,
        base_clusters_considered,
        enclosed_clusters_promoted,
        promoted_area,
        flagged_thin_kept_clusters,
        bridge_faces_reclassified,
        largest_before,
        median_before,
        largest_after,
        median_after,
        _format_material_face_histogram(hist_before),
        _format_material_face_histogram(hist_after),
    )


def color_map_faces_by_terrain(map_obj, terrain_obj, up_threshold=0.05, paint_material_name=None, return_metrics=False):
    """
    Loops through every face of map_obj.
    If face is facing upwards, raycasts upwards to see if terrain_obj is above.
    If yes, colors the face with terrain_obj's material.
    
    up_threshold = dot(normal, Z) must be greater than this (0.5 ~ 60° angle limit).
    """
    if map_obj.type != 'MESH' or terrain_obj.type != 'MESH':
        print("Both inputs must be mesh objects.")
        return

    recalculateNormals(map_obj)

    #terrain_obj.location.z += 10

    # Ensure both have mesh data
    map_mesh = map_obj.data
    terrain_mesh = terrain_obj.data

    # Build bmesh for Map
    bm = bmesh.new()
    bm.from_mesh(map_mesh)
    bm.faces.ensure_lookup_table()

    # Build BVH tree for Terrain in world space
    terrain_world = terrain_obj.matrix_world
    verts = [terrain_world @ v.co for v in terrain_mesh.vertices]
    polys = [p.vertices for p in terrain_mesh.polygons]
    bvh = bvhtree.BVHTree.FromPolygons(verts, polys)

    # Get or create a material for terrain color
    if paint_material_name:
        mat = bpy.data.materials.get(paint_material_name)
        if mat is None:
            print(f"Paint override material '{paint_material_name}' not found. Falling back to terrain material.")
    else:
        mat = None

    if mat is None:
        if terrain_obj.active_material:
            mat = terrain_obj.active_material
        else:
            mat = bpy.data.materials.new(name="TerrainColor")
            terrain_obj.data.materials.append(mat)

    # Make sure Map has material slots
    if mat.name not in [m.name for m in map_mesh.materials]:
        map_mesh.materials.append(mat)
    mat_index = map_mesh.materials.find(mat.name)

    up = Vector((0, 0, 1))
    colored_count = 0
    faces_checked_up = 0
    ray_hits = 0
    debug_samples = 5
    debug_every = max(1, len(bm.faces) // debug_samples)
    map_world = map_obj.matrix_world
    map_direction_matrix = map_world.to_3x3()

    for i, f in enumerate(bm.faces):
        normal_world = (map_direction_matrix @ f.normal).normalized()
        dot = normal_world.dot(up)
        # Only consider faces facing upward
        if dot > up_threshold:
            faces_checked_up += 1
            center = f.calc_center_median()
            center_world = map_world @ center
            primary_ray_dir = Vector((0, 0, 1))
            fallback_ray_dir = Vector((0, 0, -1))
            cast_results = []
            for cast_name, ray_dir in (("up", primary_ray_dir), ("down", fallback_ray_dir)):
                loc, norm, idx, dist = bvh.ray_cast(center_world, ray_dir, 1000)
                if loc is not None and dist is not None and dist > 1e-6:
                    cast_results.append((dist, cast_name, ray_dir, loc, norm, idx))

            if cast_results:
                dist, hit_direction_name, hit_direction_vec, loc, norm, idx = min(cast_results, key=lambda x: x[0])
            else:
                hit_direction_name = None
                hit_direction_vec = primary_ray_dir
                loc = norm = idx = dist = None

            if i % debug_every == 0:
                print(
                    f"[terrain paint debug] face={i} center_world={tuple(round(v, 4) for v in center_world)} "
                    f"ray_dir={tuple(round(v, 4) for v in hit_direction_vec)} "
                    f"hit_dir={hit_direction_name if hit_direction_name is not None else 'none'} "
                    f"dot={round(dot, 4)} "
                    f"hit={'yes' if loc is not None else 'no'} dist={round(dist, 6) if dist is not None else None}"
                )
                if loc is None:
                    module_logger.info(
                        "Terrain paint miss sample | map=%s terrain=%s face=%s center_world=(%.6f,%.6f,%.6f) normal_world=(%.6f,%.6f,%.6f) dot=%.6f hit_dir=%s hit_dist=%s",
                        map_obj.name,
                        terrain_obj.name,
                        i,
                        center_world.x,
                        center_world.y,
                        center_world.z,
                        normal_world.x,
                        normal_world.y,
                        normal_world.z,
                        dot,
                        "none",
                        "None",
                    )

            if loc is not None and dist is not None and dist > 1e-6:
                ray_hits += 1
                # Assign terrain material to this face
                f.material_index = mat_index
                colored_count += 1

    bm.to_mesh(map_mesh)
    bm.free()

    print(f"Colored {colored_count} faces on {map_obj.name} based on {terrain_obj.name}")

    if return_metrics:
        return {
            "faces_checked_up": faces_checked_up,
            "ray_hits": ray_hits,
            "faces_colored": colored_count,
            "material_name_used": mat.name if mat else None,
        }
    return None


def build_terrain_surface(map_obj):
    props = getattr(getattr(bpy.context, "scene", None), "tp3d", None)
    module_logger.info("Fetching elevation data for map %s | props.api=%s", map_obj.name if map_obj else "unknown", getattr(props, "api", None))
    bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
    module_logger.info("build_terrain_surface before get_tile_elevation | map=%s", map_obj.name if map_obj else "unknown")
    tile_verts, diff = get_tile_elevation(map_obj)
    module_logger.info("build_terrain_surface after get_tile_elevation | verts=%s | elev_range=%s", len(tile_verts), diff)
    if len(tile_verts) < 2000:
        show_message_box(f"Mesh has only {len(tile_verts)} Points. Add more Points to Increase Resolution (e.G Subdivision)", "INFO", "INFO")
    return tile_verts, diff


def collect_osm_layers(map_obj):
    layers = {}

    props = getattr(getattr(bpy.context, "scene", None), "tp3d", None)
    include_water = bool(getattr(props, "col_wActive", False))
    include_forest = bool(getattr(props, "col_fActive", False))
    include_city = bool(getattr(props, "col_cActive", False))
    include_glacier = bool(getattr(props, "col_glActive", False))

    if include_water:
        layers["WATER"] = build_coloring_layer(map_obj, "WATER")
    if include_forest:
        layers["FOREST"] = build_coloring_layer(map_obj, "FOREST")
    if include_city:
        layers["CITY"] = build_coloring_layer(map_obj, "CITY")
    if include_glacier:
        layers["GLACIER"] = build_coloring_layer(map_obj, "GLACIER")
    return layers


def apply_land_base(map_obj):
    mat = bpy.data.materials.get("BASE")
    map_obj.data.materials.clear()
    map_obj.data.materials.append(mat)

    for area in bpy.context.screen.areas:
        if area.type == 'VIEW_3D':
            for space in area.spaces:
                if space.type == 'VIEW_3D':
                    space.shading.type = 'MATERIAL'


def paint_entire_map_base(map_obj, base_material='BASE'):
    if not map_obj or map_obj.type != 'MESH' or not map_obj.data:
        return

    base_mat = bpy.data.materials.get(base_material)
    if base_mat is None:
        return

    mesh = map_obj.data
    base_index = mesh.materials.find(base_material)
    if base_index == -1:
        mesh.materials.append(base_mat)
        base_index = mesh.materials.find(base_material)

    for poly in mesh.polygons:
        poly.material_index = base_index


def apply_water_layer(map_obj, layer_objects):
    layer = layer_objects.get("WATER")
    return paint_coloring_layer(map_obj, layer) if layer else None


def apply_island_layer(map_obj, layer_objects):
    water_layer = layer_objects.get("WATER") if layer_objects else None
    island_objects = water_layer.get("island_objects") if water_layer else None
    island_count = len(island_objects) if island_objects else 0
    col_paint_map = bpy.context.scene.tp3d.col_PaintMap
    col_process_islands = bool(getattr(bpy.context.scene.tp3d, "col_ProcessIslands", True))
    module_logger.info(
        "Island layer apply start | map=%s col_PaintMap=%s col_ProcessIslands=%s island_object_count=%s",
        map_obj.name if map_obj else None,
        col_paint_map,
        col_process_islands,
        island_count,
    )
    if col_paint_map == 1 and col_process_islands:
        paint_islands_on_map(map_obj, island_objects)


def apply_overlay_layers(map_obj, layer_objects):
    return {
        "FOREST": paint_coloring_layer(map_obj, layer_objects.get("FOREST")),
        "CITY": paint_coloring_layer(map_obj, layer_objects.get("CITY")),
        "GLACIER": paint_coloring_layer(map_obj, layer_objects.get("GLACIER")),
    }


def run_layer_pipeline(map_obj):
    apply_land_base(map_obj)
    layer_objects = collect_osm_layers(map_obj)
    module_logger.info(
        "Layer paint routing | WATER=%s FOREST=%s CITY=%s GLACIER=%s via=paint_coloring_layer->color_map_faces_by_terrain",
        bool(layer_objects.get("WATER")),
        bool(layer_objects.get("FOREST")),
        bool(layer_objects.get("CITY")),
        bool(layer_objects.get("GLACIER")),
    )
    paint_entire_map_base(map_obj, base_material='BASE')
    water_obj = apply_water_layer(map_obj, layer_objects)
    apply_island_layer(map_obj, layer_objects)
    overlay_objs = apply_overlay_layers(map_obj, layer_objects)
    return {
        "water": water_obj,
        "overlays": overlay_objs,
    }


def merge_with_map(mapobject, mergeobject):

    print(mapobject.name)
    print(mergeobject.name)
    print(mergeobject.type)


    if mergeobject.type == "CURVE":
        print("MERGE CURVE WITH MAP")


        duplicate  = mapobject.copy()
        duplicate.data = mapobject.data.copy()
        bpy.context.collection.objects.link(duplicate)
        #intersect_alltrails_with_existing_box(duplicate)
        intersect_trail_with_existing_box(duplicate,mergeobject)
        return duplicate




    bpy.ops.object.select_all(action="DESELECT")

    #if the mergeobject is a Text object -> Convert it into a mesh
    if mergeobject.type == "FONT":
        mergeobject.select_set(True)
        bpy.context.view_layer.objects.active = mergeobject
        bpy.ops.object.convert(target='MESH')

    if mergeobject.type == "CURVE":
        mergeobject.select_set(True)
        bpy.context.view_layer.objects.active = mergeobject
        bpy.ops.object.convert(target='MESH')

    bpy.context.view_layer.objects.active = mergeobject
    mergeobject.select_set(True)
    bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, 200))#bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.object.mode_set(mode='OBJECT')
    mergeobject.location.z = -1

    recalculateNormals(mergeobject)
    



    # Add boolean modifier
    bool_mod = mergeobject.modifiers.new(name="Boolean", type='BOOLEAN')
    bool_mod.object = mapobject
    bool_mod.operation = 'INTERSECT'
    bool_mod.solver = 'MANIFOLD'

    #apply boolean modifier
    bpy.ops.object.modifier_apply(modifier=bool_mod.name)

    bpy.ops.object.mode_set(mode="EDIT")
    bm = bmesh.from_edit_mesh(mergeobject.data)

    bm.verts.ensure_lookup_table()
    bm.faces.ensure_lookup_table()



    try:
        min_z = min(v.co.z for v in bm.verts)
    except:
        bpy.ops.object.mode_set(mode='OBJECT')
        return
    
    tol = 0.1
    print(min_z)

    lowestVert = 100


    
    for v in bm.verts:
        if abs(v.co.z - min_z) < tol:
            v.select = True
        else:
            v.select = False
            if v.co.z < lowestVert:
                lowestVert = v.co.z
    
    print(lowestVert)

    
    bpy.context.tool_settings.mesh_select_mode = (True, False, False)
    #bmesh.ops.delete(bm, geom=[f for f in bm.faces if f.select], context="FACES")
    #bmesh.ops.delete(bm, geom=[v for v in bm.verts if not v.link_faces], context='VERTS')
    bmesh.ops.delete(bm, geom=[elem for elem in bm.verts[:] + bm.edges[:] + bm.faces[:] if elem.select], context='VERTS')

    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, -1))#bpy.ops.mesh.select_all(action='DESELECT')




    bmesh.update_edit_mesh(mergeobject.data)
    bpy.ops.object.mode_set(mode="OBJECT")

    mergeobject.location.z += 0.05

    return mergeobject
    
def midpoint_spherical(lat1, lon1, lat2, lon2):
    # Convert degrees to radians
    lat1_rad = math.radians(lat1)
    lon1_rad = math.radians(lon1)
    lat2_rad = math.radians(lat2)
    lon2_rad = math.radians(lon2)

    # Convert to Cartesian coordinates
    x1 = math.cos(lat1_rad) * math.cos(lon1_rad)
    y1 = math.cos(lat1_rad) * math.sin(lon1_rad)
    z1 = math.sin(lat1_rad)

    x2 = math.cos(lat2_rad) * math.cos(lon2_rad)
    y2 = math.cos(lat2_rad) * math.sin(lon2_rad)
    z2 = math.sin(lat2_rad)

    # Average the vectors
    x = (x1 + x2) / 2
    y = (y1 + y2) / 2
    z = (z1 + z2) / 2

    # Convert back to spherical coordinates
    lon_mid = math.atan2(y, x)
    hyp = math.sqrt(x * x + y * y)
    lat_mid = math.atan2(z, hyp)

    # Convert radians back to degrees
    return math.degrees(lat_mid), math.degrees(lon_mid)

def move_coordinates(lat, lon, distance_km, direction):
    """
    Move a point a given distance (in km) in a cardinal direction (N, S, E, W).
    """
    R = 6371.0  # Earth radius in km
    direction = direction.lower()
    
    # Convert latitude and longitude from degrees to radians
    lat_rad = math.radians(lat)
    lon_rad = math.radians(lon)

    if direction == "n":
        lat_rad += distance_km / R
    elif direction == "s":
        lat_rad -= distance_km / R
    elif direction == "e":
        lon_rad += distance_km / (R * math.cos(lat_rad))
    elif direction == "w":
        lon_rad -= distance_km / (R * math.cos(lat_rad))
    else:
        raise ValueError("Direction must be 'n', 's', 'e', or 'w'")
    
    # Convert radians back to degrees
    new_lat = math.degrees(lat_rad)
    new_lon = math.degrees(lon_rad)

    return new_lat, new_lon

def delete_non_manifold(object):

    bpy.ops.object.select_all(action="DESELECT")

    #if the mergeobject is a Text object -> Convert it into a mesh
    object.select_set(True)
    bpy.context.view_layer.objects.active = object

    # Make sure you're in edit mode
    bpy.ops.object.mode_set(mode='EDIT')

    # Get the active mesh
    obj = bpy.context.edit_object
    me = obj.data

    # Access the BMesh representation
    bm = bmesh.from_edit_mesh(me)

    # Ensure the mesh has up-to-date normals and edges
    bm.normal_update()

    # Deselect everything first (optional)
    bpy.ops.mesh.select_all(action='DESELECT')

    # Select non-manifold edges
    bpy.ops.mesh.select_non_manifold()

    # (Optional) Update the mesh to reflect selection in UI
    bmesh.update_edit_mesh(me, loop_triangles=True)

    bpy.ops.mesh.delete(type='VERT')

    bpy.ops.object.mode_set(mode='OBJECT')

def plateInsert(plate,map):

    bpy.ops.object.select_all(action="DESELECT")

    tol = bpy.context.scene.tp3d.tolerance
    dist = bpy.context.scene.tp3d.plateInsertValue

    # Duplicate the map object
    map_copy = map.copy()
    map_copy.data = map.data.copy()
    bpy.context.collection.objects.link(map_copy)
    map_copy.scale *= (size + tol) / size

    

    plate.location.z += dist


    map_copy.select_set(True)
    bpy.context.view_layer.objects.active = map_copy
    selectBottomFaces(map_copy)
    bpy.ops.mesh.select_all(action='INVERT')
    bpy.ops.mesh.delete(type='FACE')
    bpy.ops.mesh.select_all(action='SELECT')

    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, 100))#bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.object.mode_set(mode='OBJECT')

    recalculateNormals(map_copy)
    bpy.ops.object.select_all(action="DESELECT")

    plate.select_set(True)
    bpy.context.view_layer.objects.active = plate

    mod = plate.modifiers.new(name="Boolean", type='BOOLEAN')
    mod.operation = 'DIFFERENCE'
    mod.solver = "MANIFOLD"
    mod.object = map_copy

    bpy.ops.object.modifier_apply(modifier = mod.name)
    
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR')

    bpy.data.objects.remove(map_copy, do_unlink=True)

def selectBottomFaces(obj):

    if obj is None or obj.type != 'MESH':
        raise Exception("Please select a mesh object.")


    # Enter Edit Mode
    bpy.ops.object.mode_set(mode='EDIT')
    mesh = bmesh.from_edit_mesh(obj.data)

    # Recalculate normals
    bmesh.ops.recalc_face_normals(mesh, faces=mesh.faces)

    # Threshold for downward-facing
    threshold = -0.99

    # Object world matrix for local-to-global transformation
    world_matrix = obj.matrix_world


    for f in mesh.faces:
        if f.normal.normalized().z < threshold:
            f.select = True  # Optional: visually select in viewport
        else:
            f.select = False

    # Update the mesh
    bmesh.update_edit_mesh(obj.data, loop_triangles=False)

def selectTopFaces(obj):
    if obj is None or obj.type != 'MESH':
        raise Exception("Please select a mesh object.")


    # Enter Edit Mode
    bpy.ops.object.mode_set(mode='EDIT')
    mesh = bmesh.from_edit_mesh(obj.data)

    # Recalculate normals
    bmesh.ops.recalc_face_normals(mesh, faces=mesh.faces)

    # Threshold for downward-facing
    threshold = 0.99

    # Object world matrix for local-to-global transformation
    world_matrix = obj.matrix_world


    for f in mesh.faces:
        if f.normal.normalized().z > threshold:
            f.select = True  # Optional: visually select in viewport
        else:
            f.select = False

    # Update the mesh
    bmesh.update_edit_mesh(obj.data, loop_triangles=False)

def set_origin_to_3d_cursor(tobj=None):
    if tobj is None:
        tobj = bpy.context.active_object

    bpy.ops.object.select_all(action='DESELECT')

    bpy.context.view_layer.objects.active = tobj
    tobj.select_set(True)
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR')

def recalculateNormals(obj):
    mesh = obj.data

    bm = bmesh.new()
    bm.from_mesh(mesh)

    # recalc normals outward
    bmesh.ops.recalc_face_normals(bm, faces=bm.faces)

    bm.to_mesh(mesh)
    bm.free()
    mesh.update()

def writeMetadata(obj, type = "MAP"):


    if type == "MAP":
        obj["Object type"] = type
        obj["Addon"] = category
        obj["Version"] = str(AddonVersion[0]) + "," + str(AddonVersion[1])

        obj["Generation Duration"] = str( duration) + " seconds"
        obj["Shape"] = bpy.context.scene.tp3d.shape
        obj["Resolution"] = bpy.context.scene.tp3d.num_subdivisions
        obj["Elevation Scale"] = bpy.context.scene.tp3d.scaleElevation
        obj["objSize"] = bpy.context.scene.tp3d.objSize
        obj["pathThickness"] = round(bpy.context.scene.tp3d.pathThickness,2)
        obj["overwritePathElevation"] = bpy.context.scene.tp3d.overwritePathElevation
        obj["api"] = bpy.context.scene.tp3d.api
        obj["scalemode"] = bpy.context.scene.tp3d.scalemode
        obj["fixedElevationScale"] = bpy.context.scene.tp3d.fixedElevationScale
        obj["minThickness"] = bpy.context.scene.tp3d.minThickness
        obj["xTerrainOffset"] = bpy.context.scene.tp3d.xTerrainOffset
        obj["yTerrainOffset"] = bpy.context.scene.tp3d.yTerrainOffset
        obj["singleColorMode"] = bpy.context.scene.tp3d.singleColorMode
        obj["selfHosted"] = bpy.context.scene.tp3d.selfHosted
        obj["Horizontal Scale"] = round(bpy.context.scene.tp3d.sScaleHor,6)
        obj["Generate Water"] = bpy.context.scene.tp3d.col_wActive
        obj["Process Water Islands"] = bpy.context.scene.tp3d.col_ProcessIslands
        obj["MinWaterSize"] = bpy.context.scene.tp3d.col_wArea
        obj["Keep Non-Manifold"] = bpy.context.scene.tp3d.col_KeepManifold
        obj["Map Size in Km"] = round(bpy.context.scene.tp3d.sMapInKm,2)
        obj["Dovetail"] = False
        obj["MagnetHoles"] = False
        obj["BottomMark"] = False
        obj["AdditionalExtrusion"] = additionalExtrusion
        obj["lowestZ"] = lowestZ
        obj["highestZ"] = highestZ
        obj["dataset"] = bpy.context.scene.tp3d.dataset
        obj["name"] = bpy.context.scene.tp3d.name
        obj["pathScale"] = bpy.context.scene.tp3d.pathScale
        obj["scaleLon1"] = bpy.context.scene.tp3d.scaleLon1
        obj["scaleLat1"] = bpy.context.scene.tp3d.scaleLat1
        obj["scaleLon2"] = bpy.context.scene.tp3d.scaleLon2
        obj["scaleLat2"] = bpy.context.scene.tp3d.scaleLat2

        obj["shapeRotation"] = bpy.context.scene.tp3d.shapeRotation
        obj["pathVertices"] = bpy.context.scene.tp3d.o_verticesPath
        obj["mapVertices"] = bpy.context.scene.tp3d.o_verticesMap
        obj["mapScale"] = bpy.context.scene.tp3d.o_mapScale
        obj["centerx"] = bpy.context.scene.tp3d.o_centerx
        obj["centery"] = bpy.context.scene.tp3d.o_centery
        obj["sElevationOffset"] = bpy.context.scene.tp3d.sElevationOffset
        obj["sMapInKm"] = bpy.context.scene.tp3d.sMapInKm

        obj["col_wActive"] = bpy.context.scene.tp3d.col_wActive
        obj["col_wArea"] = bpy.context.scene.tp3d.col_wArea
        obj["col_ProcessIslands"] = bpy.context.scene.tp3d.col_ProcessIslands
        obj["col_fActive"] = bpy.context.scene.tp3d.col_fActive
        obj["col_fArea"] = bpy.context.scene.tp3d.col_fArea
        obj["col_cActive"] = bpy.context.scene.tp3d.col_cActive
        obj["col_cArea"] = bpy.context.scene.tp3d.col_cArea
        obj["col_glActive"] = bpy.context.scene.tp3d.col_glActive
        obj["col_glArea"] = bpy.context.scene.tp3d.col_glArea 



    if type =="TRAIL":
        obj["Object type"] = type
        obj["Addon"] = category
        obj["Version"] = str(AddonVersion[0]) + "," + str(AddonVersion[1])

        obj["overwritePathElevation"] = bpy.context.scene.tp3d.overwritePathElevation
    
    if type == "CITY" or type == "WATER" or type == "FOREST":
        obj["Object type"] = type
        obj["Addon"] = category
        obj["Version"] = str(AddonVersion[0]) + "," + str(AddonVersion[1])
        obj["minThickness"] = bpy.context.scene.tp3d.minThickness

    if type == "PLATE":
        obj["Object type"] = type
        obj["Addon"] = category
        obj["Version"] = str(AddonVersion[0]) + "," + str(AddonVersion[1])
        obj["Shape"] = bpy.context.scene.tp3d.shape
        obj["textFont"] = bpy.context.scene.tp3d.textFont
        obj["textSize"] = bpy.context.scene.tp3d.textSize
        obj["overwriteLength"] = bpy.context.scene.tp3d.overwriteLength
        obj["overwriteHeight"] = bpy.context.scene.tp3d.overwriteHeight
        obj["overwriteTime"] = bpy.context.scene.tp3d.overwriteTime
        obj["outerBorderSize"] = bpy.context.scene.tp3d.outerBorderSize
        obj["shapeRotation"] = bpy.context.scene.tp3d.shapeRotation
        obj["name"] = bpy.context.scene.tp3d.name
        obj["plateThickness"] = bpy.context.scene.tp3d.plateThickness
        obj["plateInsertValue"] = bpy.context.scene.tp3d.plateInsertValue
        obj["textAngle"] = bpy.context.scene.tp3d.text_angle_preset
        obj["objSize"] = bpy.context.scene.tp3d.objSize * ((100 + bpy.context.scene.tp3d.outerBorderSize)/100)
        obj["MagnetHoles"] = False
        obj["Dovetail"] = False
    
    if type == "LINES":
        obj["Object type"] = type
        obj["cl_thickness"] = bpy.context.scene.tp3d.cl_thickness
        obj["cl_distance"] = bpy.context.scene.tp3d.cl_distance
        obj["cl_offset"] = bpy.context.scene.tp3d.cl_offset

    


def _normalize_popup_icon(icon_name, fallback="ERROR"):
    """Return a Blender-safe popup icon enum, with compatibility fallbacks."""
    if not icon_name:
        return fallback

    icon = str(icon_name).upper()

    # Compatibility aliases for historical values used across Blender versions.
    legacy_aliases = {
        "WARNING": "ERROR",
        "WARN": "ERROR",
        "INFO": "QUESTION",
    }
    icon = legacy_aliases.get(icon, icon)

    # Prefer runtime validation against Blender's current enum set when available.
    popup_fn = getattr(bpy.types.WindowManager, "popup_menu", None)
    try:
        if popup_fn and hasattr(popup_fn, "keywords") and "icon" in popup_fn.keywords:
            enum_items = popup_fn.keywords["icon"].enum_items.keys()
            if icon in enum_items:
                return icon
            if fallback in enum_items:
                return fallback
            if "NONE" in enum_items:
                return "NONE"
    except Exception:
        pass

    # Final defensive fallback for unexpected API changes.
    return fallback


def show_message_box(message, ic = "ERROR", ti = "ERROR"):
    #toggle_console()
    def draw(self, context):
        self.layout.label(text=message)
    print(message)

    safe_icon = _normalize_popup_icon(ic)

    def _popup_in_valid_window():
        wm = getattr(bpy.context, "window_manager", None)
        if not wm:
            module_logger.warning("Unable to open popup (no window manager). title=%s icon=%s message=%s", ti, safe_icon, message)
            return None

        # Use an actual UI window when current context has none (common in timers/background callbacks).
        win = getattr(bpy.context, "window", None)
        if not win and getattr(wm, "windows", None):
            try:
                win = wm.windows[0]
            except Exception:
                win = None

        if not win:
            module_logger.warning("Unable to open popup (no active window context). title=%s icon=%s message=%s", ti, safe_icon, message)
            return None

        try:
            with bpy.context.temp_override(window=win):
                wm.popup_menu(draw, title=ti, icon=safe_icon)
        except Exception:
            module_logger.exception("Failed to open popup message. title=%s icon=%s message=%s", ti, safe_icon, message)
        return None

    try:
        # Defer into Blender's UI loop so popups are executed on a safe UI context.
        bpy.app.timers.register(_popup_in_valid_window, first_interval=0.0)
    except Exception:
        module_logger.exception("Failed to schedule popup message. title=%s icon=%s message=%s", ti, safe_icon, message)

def toggle_console():
    try:
        if platform.system() == "Windows":
            bpy.ops.wm.console_toggle()
    except Exception as e:
        print(f"Could not toggle console: {e}")
    
@log_workflow
def runGeneration(type):   

    #CHECK BLENDER VERSION
    # Minimum required version
    required_version = (4, 5, 0)

    if bpy.app.version < required_version:
        show_message_box(f"TrailPrint3D 2.1 requires Blender {required_version[0]}.{required_version[1]} or higher. (you are using {bpy.app.version_string}).  ")
        return
    
    start_time = time.time()
    init_module_logger(bpy.context)

    toggle_console()
    
    for i in range(30):
        print(" ")
    print("------------------------------------------------")
    print("SCRIPT STARTED - DO NOT CLOSE THIS WINDOW")
    print("------------------------------------------------")
    print(" ")

    # Path to your GPX file
    global gpx_file_path
    gpx_file_path = bpy.context.scene.tp3d.get('file_path', None)
    global gpx_chain_path
    gpx_chain_path = bpy.context.scene.tp3d.get('chain_path', None)
    global exportPath
    exportPath = bpy.context.scene.tp3d.get('export_path', None)
    global shape
    shape = (bpy.context.scene.tp3d.shape)
    global name
    name = bpy.context.scene.tp3d.get('trailName', "")
    global size
    size =  bpy.context.scene.tp3d.get('objSize', 100)
    global num_subdivisions
    num_subdivisions = bpy.context.scene.tp3d.get('num_subdivisions', 4)
    global scaleElevation
    scaleElevation = bpy.context.scene.tp3d.get('scaleElevation', 10)
    global pathThickness
    pathThickness = bpy.context.scene.tp3d.get('pathThickness', 1.2)
    global scalemode
    scalemode = bpy.context.scene.tp3d.scalemode
    global pathScale
    pathScale = bpy.context.scene.tp3d.get('pathScale', 0.8)
    global scaleLon1
    scaleLon1 = bpy.context.scene.tp3d.get('scaleLon1', 0)
    global scaleLat1
    scaleLat1 = bpy.context.scene.tp3d.get('scaleLat1', 0)
    global scaleLon2
    scaleLon2 = bpy.context.scene.tp3d.get('scaleLon2', 0)
    global scaleLat2
    scaleLat2 = bpy.context.scene.tp3d.get('scaleLat2', 0)
    global shapeRotation
    shapeRotation = bpy.context.scene.tp3d.get('shapeRotation', 0)
    global overwritePathElevation
    overwritePathElevation = bpy.context.scene.tp3d.get('overwritePathElevation', True)
    global api
    api = bpy.context.scene.tp3d.get('api',2)
    global dataset
    #dataset_int = bpy.context.scene.tp3d.get("dataset",1)
    dataset = bpy.context.scene.tp3d.dataset
    global selfHosted
    selfHosted = bpy.context.scene.tp3d.get("selfHosted","")
    global fixedElevationScale
    fixedElevationScale = bpy.context.scene.tp3d.get('fixedElevationScale', False)
    global minThickness
    minThickness = bpy.context.scene.tp3d.get("minThickness",2)
    global xTerrainOffset
    xTerrainOffset = bpy.context.scene.tp3d.get("xTerrainOffset",0)
    global yTerrainOffset
    yTerrainOffset = bpy.context.scene.tp3d.get("yTerrainOffset",0)
    global singleColorMode
    singleColorMode = bpy.context.scene.tp3d.get("singleColorMode",0)
    global disableCache
    disableCache = bpy.context.scene.tp3d.get("disableCache",0)
    global cacheSize
    cacheSize = bpy.context.scene.tp3d.get("ccacheSize",50000)

    #OTHER VARIABLES FOR TEXT BASED SHAPES
    #Add input fields
    global textFont
    textFont = bpy.context.scene.tp3d.get("textFont","")
    global textSize
    textSize = bpy.context.scene.tp3d.get("textSize",10)
    global overwriteLength
    overwriteLength = bpy.context.scene.tp3d.get("overwriteLength","")
    global overwriteHeight
    overwriteHeight = bpy.context.scene.tp3d.get("overwriteHeight","")
    global overwriteTime
    overwriteTime = bpy.context.scene.tp3d.get("overwriteTime","")
    global outerBorderSize
    outerBorderSize = bpy.context.scene.tp3d.get("outerBorderSize",20)
    global text_angle_preset
    text_angle_preset = int(bpy.context.scene.tp3d.text_angle_preset)
    global plateThickness
    plateThickness = bpy.context.scene.tp3d.get("plateThickness",5)

    col_wActive = (bpy.context.scene.tp3d.col_wActive)
    col_fActive = (bpy.context.scene.tp3d.col_fActive)
    col_cActive = (bpy.context.scene.tp3d.col_cActive)
    col_glActive = (bpy.context.scene.tp3d.col_glActive)

    global jMapLat
    jMapLat = bpy.context.scene.tp3d.get("jMapLat",49)
    global jMapLon
    jMapLon = bpy.context.scene.tp3d.get("jMapLon",9)
    global jMapRadius
    jMapRadius = bpy.context.scene.tp3d.get("jMapRadius",50)

    global jMapLat1
    jMapLat1 = bpy.context.scene.tp3d.get("jMapLat1",48)
    global jMapLon1
    jMapLon1 = bpy.context.scene.tp3d.get("jMapLon1",8)
    global jMapLat2
    jMapLat2 = bpy.context.scene.tp3d.get("jMapLat2",49)
    global jMapLon2
    jMapLon2 = bpy.context.scene.tp3d.get("jMapLon2",9)


    global buggyDataset
    buggyDataset = 0

    global exportformat
    exportformat = "STL"
    


    global opentopoAdress
    opentopoAdress = "https://api.opentopodata.org/v1/"
    if selfHosted != "" and selfHosted != None and api == 1:
        opentopoAdress = selfHosted
        module_logger.info("Using self-hosted OpenTopo endpoint: %s", opentopoAdress)
    
    

    
    #CHECK FOR VALID INPUTS
    if type == 0 or type == 4:
        
        if not gpx_file_path or gpx_file_path == "":
            show_message_box("File path is empty! Please select a valid file.")
            toggle_console()
            return
        
        if not os.path.isfile(gpx_file_path):
            show_message_box(f"Invalid file path: {gpx_file_path}. Please select a valid file.")
            toggle_console()
            return
        gpx_file_path = bpy.path.abspath(gpx_file_path)

        file_extension = os.path.splitext(gpx_file_path)[1].lower()
        if file_extension != '.gpx' and file_extension != ".igc":
            show_message_box(f"Invalid file format. Please Use a .GPX file")
            toggle_console()
            return
    
    if type == 1:
        if not gpx_chain_path or gpx_chain_path == "":
            show_message_box("CHAIN path is empty! Please select a valid folder.")
            toggle_console()
            return
        gpx_chain_path = bpy.path.abspath(gpx_chain_path)
    if type == 2:
        #check if inputs are valid
        pass
    if type == 3:
        #check if inputs are valid
        pass
    if exportPath == None:
        show_message_box("Export path cant be empty")
        toggle_console()
        return
    
    exportPath = bpy.path.abspath(exportPath)

    if not exportPath or exportPath == "":
        show_message_box("Export path is empty! Please select a valid folder.")
        toggle_console()
        return
    if not os.path.isdir(exportPath):
        show_message_box(f"Invalid export Directory: {exportPath}. Please select a valid Directory.")
        toggle_console()
        return


    if textFont == "":
        if platform.system() == "Windows":
            textFont = "C:/WINDOWS/FONTS/ariblk.ttf"
        elif platform.system() == "Darwin":
            textFont = "/System/Library/Fonts/Supplemental/Arial Black.ttf"
        else:
            textFont = ""
            #show_message_box(f"Please select a font in the Shape Settings Tab.")
            #toggle_console()
            #return
        
    
    if name == "":
        if type == 0 or type == 4:
            name_with_ext = os.path.basename(gpx_file_path)
            name = os.path.splitext(name_with_ext)[0]
        if type == 1:
            name_with_ext = os.path.basename(os.path.normpath(gpx_chain_path))
            name = os.path.splitext(name_with_ext)[0]
        if type == 2 or type == 3:
            name = "T"
        
    #GENERATE COLORS IF THEY ARENT THERE YET
    setupColors()
        
    #CONSOLE MESSAGES
    if disableCache == 1:
        module_logger.info("Cache Disabled (in Advanced Settings)")
    if overwritePathElevation == True and singleColorMode == False:
        module_logger.info("Overwrite Path Elevation enabled")
    if type == 0 or type == 1 or type == 4:
        if xTerrainOffset > 0:
            module_logger.info("Map xTerrainOffset=%s", xTerrainOffset)
        if yTerrainOffset > 0:
            module_logger.info("Map yTerrainOffset=%s", yTerrainOffset)

    
    if singleColorMode == True:
        #overwritePathElevation = False
        module_logger.info("SingleColorMode active")

    #STARTSETTINGS
    #Leave edit mode      
    if bpy.context.object and bpy.context.object.mode == 'EDIT':
        bpy.ops.object.mode_set(mode='OBJECT')

    # Disable Auto Merge Vertices
    bpy.context.scene.tool_settings.use_mesh_automerge = False
        
    coordinates = []
    coordinates2 = []
    tempcoordinates = []
    separate_paths = []
    blender_coords_separate = []
    # Load GPX data       
    if 1 == 1: 
    #try:
        if type == 0:
            
            separate_paths = read_gpx_file()
        if type == 1:
            separate_paths = read_gpx_directory(gpx_chain_path)
        if type == 2 or type == 4:
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"e")
            separate_paths.append([(nlat,nlon,0,0)])
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"s")
            separate_paths.append([(nlat,nlon,0,0)])
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"w")
            separate_paths.append([(nlat,nlon,0,0)])
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"n")
            separate_paths.append([(nlat,nlon,0,0)])

            print(separate_paths)

            if type == 4:
                tempcoordinates = read_gpx_file()
                coordinates2 = [item for sublist in tempcoordinates for item in sublist]

        if type == 3:
            separate_paths.append([(jMapLat1,jMapLon1,0,0)])
            separate_paths.append([(jMapLat2,jMapLon2,0,0)])
    #except Exception as e:
    else:
        show_message_box(f"Something went Wrong reading the GPX. Type {type}")
        return
    coordinates = [item for sublist in separate_paths for item in sublist]
    #coordinates = separate_paths

    #print(f"separaite paits: {len(separate_paths)}")
    


    
    #Calculating some Stats about the path
    global total_length
    global total_elevation
    global total_time
    total_length = 0
    total_elevation = 0
    total_time = 0
    if type == 0 or type == 1:
        total_length = calculate_total_length(coordinates)
        total_elevation = calculate_total_elevation(coordinates)
        total_time = calculate_total_time(coordinates)


    hours = int(total_time)
    minutes = int((total_time - hours) * 60)
    global time_str
    time_str = f"{hours}h {minutes}m"

    while len(coordinates) < 300 and len(coordinates) > 1 and type != 2:
        i = 0
        while i < len(coordinates) - 1:
            p1 = coordinates[i]
            p2 = coordinates[i + 1]

            # Calculate midpoint (only for x, y, z)
            midpoint = (
                (p1[0] + p2[0]) / 2,
                (p1[1] + p2[1]) / 2,
                (p1[2] + p2[2]) / 2,
                (p1[3])  # Optional: interpolate time too
            )

            # Insert midpoint before p2
            coordinates.insert(i + 1, midpoint)

            # Skip over the new point and the original next point
            i += 2
    

    #CALCULATE biggest distance so you can calculate the value for the smoothing
    min_x = max(point[0] for point in coordinates)
    max_x = max(point[0] for point in coordinates)
    min_y = min(point[1] for point in coordinates)
    max_y = max(point[1] for point in coordinates)
    p1 = convert_to_blender_coordinates(min_x, min_y, 0,"")
    p2 = convert_to_blender_coordinates(max_x,max_y, 0,"")

    distance = math.sqrt((p2[0] - p1[0]) ** 2 + (p2[1] - p1[1]) ** 2)


    
    #CALCULATE SCALE 
    global scaleHor

    scalecoords = coordinates
    if scalemode == "COORDINATES" and (type == 0 or type == 1):
        c2 = ((scaleLon1,scaleLat1),(scaleLon2,scaleLat2))
        scalecoords = c2


    scaleHor = calculate_scale(size, scalecoords, type)
    print(f"scaleHor: {scaleHor}")

    bpy.context.scene.tp3d["sScaleHor"] = scaleHor
    

    

    # Convert coordinates to Blender format and create a curve
    #print("Converting Coordinates to Blender format coordinates for X and Y coordsd")
    blender_coords = [convert_to_blender_coordinates(lat, lon, ele,timestamp) for lat, lon, ele, timestamp in coordinates]
    
    if type == 1 or len(separate_paths) > 1:
        blender_coords_separate = [
            [convert_to_blender_coordinates(lat, lon, ele, timestamp) for lat, lon, ele, timestamp in path]
            for path in separate_paths
            ]

  
    
    #CALCULATE CENTER
    min_x = min(point[0] for point in blender_coords)
    max_x = max(point[0] for point in blender_coords)
    min_y = min(point[1] for point in blender_coords)
    max_y = max(point[1] for point in blender_coords)
    
    global centerx
    global centery
    centerx = (max_x-min_x)/2 + min_x
    centery = (max_y-min_y)/2 + min_y

    #if type == 2:
    #centerx,centery,z = convert_to_blender_coordinates(jMapLat,jMapLon,0,0)


    bpy.context.scene.tp3d["o_centerx"] = centerx
    bpy.context.scene.tp3d["o_centery"] = centery

    #print(f"CenterX: {centerx}, CenterY: {centery}")
    
    #DELETE OBJECTS THAT SIT AT THE CENTER TO PREVENT OVERLAPPING
    target_location_2d = Vector((centerx,centery))
    target_location_2d_offset = Vector((centerx + xTerrainOffset, centery + yTerrainOffset))
    for obs in bpy.data.objects:
        obj_location_2d = Vector((obs.location.x, obs.location.y))
        if (obj_location_2d - target_location_2d).length <= 0.1 or (obj_location_2d - target_location_2d_offset).length <= 0.1:
            bpy.data.objects.remove(obs, do_unlink = True)
            print("deleted overlapping object (Previous generated objects)")

    bpy.ops.object.select_all(action='DESELECT')

    global MapObject
    # CREATE SHAPES
    #print("Creating MapObject")
    if shape == "HEXAGON": #hexagon
        MapObject = create_hexagon(size/2)
    elif shape == "SQUARE": #rectangle
        MapObject = create_rectangle(size,size)
    elif shape == "HEXAGON INNER TEXT": #Hexagon with inner text
        MapObject = create_hexagon(size/2)
    elif shape == "HEXAGON OUTER TEXT": #Hexagon with outer text
        MapObject = create_hexagon(size/2)
    elif shape == "HEXAGON FRONT TEXT": #Hexagon with front text
        MapObject = create_hexagon(size/2)
    else:
        MapObject = create_hexagon(size/2)
    
    recalculateNormals(MapObject)

    
    #SHAPE ROTATION
    MapObject.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    MapObject.select_set(True)
    bpy.context.view_layer.objects.active = MapObject
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)

    targetx = centerx + xTerrainOffset
    targety = centery + yTerrainOffset
    #print(f"targetx: {targetx}, targety: {targety}")
    if scalemode == "COORDINATES" and type == 1:
        midLat, midLon = midpoint_spherical(scaleLat1,scaleLon1,scaleLat2,scaleLon2)
        targetx, targety, el = convert_to_blender_coordinates(midLat,midLon,0,0)
    #print(f"targetx: {targetx}, targety: {targety}")

    transform_MapObject(MapObject, targetx, targety)

    if type == 4:
        coordinates = coordinates2
    

    #fetch and apply the elevation
    global autoScale
    tileVerts, diff = build_terrain_surface(MapObject)
    
    if fixedElevationScale == True:
        if diff > 0:
            autoScale = 10/(diff/1000)
        else:
            autoScale = 10
    else:
        autoScale = scaleHor
    
    bpy.context.scene.tp3d["sAutoScale"] = autoScale



    if fixedElevationScale == False:
        if diff == 0:
            pass
            show_message_box("Terrain seems to be really Flat. Might not have Elevation data for that Region. Try Diffrent Api or diffrent Datasets", "INFO", "INFO")
        elif (diff/1000) * autoScale * scaleElevation < 2 :
            show_message_box("Terrain seems to be Flat. Increasing ScaleElevation could helpk", "INFO", "INFO")

    
    #RECALCULATE THE COORDS WITH AUTOSCALE APPLIED
    blender_coords = [convert_to_blender_coordinates(lat, lon, ele,timestamp) for lat, lon, ele, timestamp in coordinates]

    target_spacing = max(0.12, 0.35 * pathThickness)
    blender_coords = resample_path_spacing(blender_coords, target_spacing)
    blender_coords = simplify_curve(blender_coords, .12)

    #PREVENT CLIPPING OF IDENTICAL COORDINATES
    blender_coords = separate_duplicate_xy(blender_coords, 0.05) 
    
    if (type == 1 or len(separate_paths) > 1) and type != 4:
        blender_coords_separate = [
            resample_path_spacing(
                [convert_to_blender_coordinates(lat, lon, ele, timestamp) for lat, lon, ele, timestamp in path],
                target_spacing
            )
            for path in separate_paths
            ]
    
    #calculate real Scale
    tdist = 0
    lat1 = coordinates[0][0]
    lon1 = coordinates[0][1]
    lat2 = coordinates[-1][0]
    lon2 = coordinates[-1][1]
    tdist = haversine(lat1,lon1 ,lat2 , lon2)
    #print(f"lat1: {lat1} | lon1: {lon1} ||| lat2: {lat2} | lon2: {lon2}")
    #print(f"tdist:{tdist}")
    mscale = (tdist/size) * 1000000
    #print(f"scale: {mscale}")
    bpy.context.scene.tp3d["o_mapScale"] = f"{mscale:.0f}"

    path_max_len = 0.5 * pathThickness
    blender_coords = densify_path_segments(blender_coords, path_max_len)

    if blender_coords_separate:
        blender_coords_separate = [
            densify_path_segments(path_coords, path_max_len) for path_coords in blender_coords_separate
        ]

    #------------------------------------------------------------------------------------------------------------------------
    #CREATE THE PATH
    #print("Creating Curve")
    global curveObj
    curveObj = None

    print("YES=")
    print(f"paths: {len(blender_coords_separate)}")
    #if 1 == 1:
    try:
        if (type == 0 and len(blender_coords_separate) <= 1) and type != 2 or type == 4:
            #print(blender_coords)
            print("YES")
            create_curve_from_coordinates(blender_coords)
            curveObj = bpy.context.view_layer.objects.active
        elif (type == 1 or len(blender_coords_separate) > 1) and type != 4 and type != 2:
            for crds in blender_coords_separate:
                create_curve_from_coordinates(crds)
                
                bpy.ops.object.join()
                curveObj = bpy.context.view_layer.objects.active
    except Exception as e:
    #else:
        show_message_box("Bad Response from API while creating the curve. If this happens everytime contact dev")
        return
    
    
    bpy.ops.object.select_all(action='DESELECT')
    
    
    #APPLY TERRAIN ELEVATION
    mesh = MapObject.data

    global lowestZ
    global highestZ  
    lowestZ = 1000
    highestZ = 0
    for i, vert in enumerate(mesh.vertices):
        vert.co.z = (tileVerts[i] - elevationOffset)/1000 * scaleElevation * autoScale
        if vert.co.z < lowestZ:
            lowestZ = vert.co.z
        if vert.co.z > highestZ:
            highestZ = vert.co.z
            
    global additionalExtrusion
    additionalExtrusion = lowestZ

    bpy.context.scene.tp3d["sAdditionalExtrusion"] = additionalExtrusion
    bpy.context.view_layer.objects.active = MapObject
    bpy.ops.object.transform_apply(location = False, rotation = True, scale = True)
    bpy.context.view_layer.update()
    
    #Raycast the curve points onto the Mesh surface
    if overwritePathElevation == True and curveObj != None:
        if MapObject and MapObject.type == 'MESH' and MapObject.data and len(MapObject.data.polygons) > 0:
            RaycastCurveToMesh(curveObj, MapObject)
        else:
            module_logger.warning("Skipping path elevation overwrite: map object is not a valid mesh")

    # Extrude hexagon to z=0 and scale bottom face
    #bpy.context.scene.tool_settings.transform_pivot_point = 'CURSOR'
    bpy.context.view_layer.objects.active = MapObject
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.mesh.dissolve_faces() #Merge the bottom faces to a single face
    bpy.ops.transform.translate(value=(0, 0, -1))#bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.object.mode_set(mode='OBJECT')

    global obj
    obj = bpy.context.object


    # Get the mesh data
    mesh = obj.data
    # Get selected faces
    selected_faces = [face for face in mesh.polygons if face.select]
    
    
    if selected_faces:
        for face in selected_faces:
            for vert_idx in face.vertices:
                vert = mesh.vertices[vert_idx]
                vert.co.z = additionalExtrusion - minThickness
    else:
        print("No face selected.")
    
    #CHANGE OBJECT ORIGIN
    bpy.context.view_layer.objects.active = MapObject
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.transform.translate(value=(0, 0, -additionalExtrusion+minThickness))#bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.object.mode_set(mode='OBJECT')

    if curveObj:
        bpy.context.view_layer.objects.active = curveObj
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.curve.select_all(action='SELECT')
        bpy.ops.transform.translate(value=(0, 0, -additionalExtrusion+minThickness))#bpy.ops.mesh.select_all(action='DESELECT')
        bpy.ops.object.mode_set(mode='OBJECT')

    
    
    #sets 3D cursor to origin of tile
    location = obj.location
    bpy.context.scene.cursor.location = location
    if curveObj:
        curveObj.select_set(True)
        bpy.ops.object.origin_set(type="ORIGIN_CURSOR")
    
    #Set tile as parent to path
    #curveObj.parent = obj
    #curveObj.matrix_parent_inverse = obj.matrix_world.inverted()
    
    recalculateNormals(obj)


    #ADDITIONAL SHAPE STUFF
    if shape == "HEXAGON INNER TEXT":
        HexagonInnerText()
    if shape == "HEXAGON OUTER TEXT":
        HexagonOuterText()
        obj.location.z += plateThickness
        curveObj.location.z += plateThickness
    if shape == "OCTAGON OUTER TEXT":
        OctagonOuterText()
        obj.location.z += plateThickness
        curveObj.location.z += plateThickness
    if shape == "HEXAGON FRONT TEXT":
        HexagonFrontText()
        obj.location.z += plateThickness
        curveObj.location.z += plateThickness
    else:
        pass
        #BottomText()
        


    #PLATESHAPE INSERT
    bpy.ops.object.select_all(action='DESELECT')
    dist = bpy.context.scene.tp3d.plateInsertValue
    if shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
        #plate = bpy.data.objects.get(name + "_Plate")
        #text = bpy.data.objects.get(name + "_Text")
        plate = plateobj
        text = textobj
        if dist > 0:
            plateInsert(plate, obj)
            text.location.z += dist
        print("SHeesh")
        print(xTerrainOffset)
        print(yTerrainOffset)
        transform_MapObject(plate, xTerrainOffset, yTerrainOffset)
        transform_MapObject(text, xTerrainOffset, yTerrainOffset)
        set_origin_to_3d_cursor(plate)
        set_origin_to_3d_cursor(text)
        if shapeRotation != 0:
            text.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    
    
    layer_pipeline_result = run_layer_pipeline(obj)
    objWater = layer_pipeline_result["water"]
    overlay_layers = layer_pipeline_result["overlays"]
    objForest = overlay_layers.get("FOREST")
    objCity = overlay_layers.get("CITY")
    objGlacier = overlay_layers.get("GLACIER")


    
    #bpy.ops.object.select_all(action='DESELECT')
    #obj.select_set(True)
    #SINGLE COLOR

    if singleColorMode == 1:
        single_color_mode(curveObj,obj.name)

    #SCM for Elements Currently Paused because it doesnt work if the Water object is Non-manifold
    #    if col_wActive == 1 and objWater != None:
    #        single_color_mode(objWater,obj.name)


    if curveObj:
        mat = bpy.data.materials.get("TRAIL")
        curveObj.data.materials.clear()
        curveObj.data.materials.append(mat)


    #ZOOM TO OBJECT
    zoom_camera_to_selected(obj)
    
    bpy.ops.object.select_all(action='DESELECT')    
    

    #EXPORT STL
    if curveObj:
        export_to_STL(curveObj,exportformat)
    export_to_STL(obj, exportformat)
    
    if shape == "HEXAGON INNER TEXT" or shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
        tobj = textobj
        mat = bpy.data.materials.get("WHITE")
        if shape == "HEXAGON INNER TEXT":
            mat = bpy.data.materials.get("TRAIL")
        tobj.data.materials.clear()
        tobj.data.materials.append(mat)
        export_to_STL(tobj, exportformat)
    if shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
        plobj = plateobj
        mat = bpy.data.materials.get("BLACK")
        plobj.data.materials.clear()
        plobj.data.materials.append(mat)
        writeMetadata(plobj, type = "PLATE")
        export_to_STL(plobj, exportformat)
    
    
    end_time = time.time()
    duration = end_time - start_time
    
    bpy.context.scene.tp3d["o_time"] = f"Script ran for {duration:.0f} seconds"


    #STORE VALUES IN MAP
    writeMetadata(obj)

    if type != 2:
        writeMetadata(curveObj,"TRAIL")
    
    #API Counter updaten
    count_openTopoData, last_date_openTopoData, count_openElevation, last_date_openElevation  = load_counter()
    if count_openTopoData < 1000:
        bpy.context.scene.tp3d["o_apiCounter_OpenTopoData"] = f"API Limit: {count_openTopoData:.0f}/1000 daily"
    else:
        bpy.context.scene.tp3d["o_apiCounter_OpenTopoData"] = f"API Limit: {count_openTopoData:.0f}/1000 (daily limit reached. might cause problems)"
    
    if count_openElevation < 1000:
        bpy.context.scene.tp3d["o_apiCounter_OpenElevation"] = f"API Limit: {count_openElevation:.0f}/1000 Monthly"
    else:
        bpy.context.scene.tp3d["o_apiCounter_OpenElevation"] = f"API Limit: {count_openElevation:.0f}/1000 (Monthly limit reached. might cause problems)"
        
    
    if buggyDataset != 0:
        show_message_box(f"API seems to have faulty Data. Try diffrent Resolution or API")
        
    print(f"Finished")

    toggle_console()
