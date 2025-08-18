#                                                           #
# Aplicación interactiva para el conteo automático de esporas,
# células, nanoestructuras o microestructuras en imágenes   #
# microscópicas, con herramientas de procesamiento de imagen#
# y ajustes personalizados para mejorar la detección y      #
# segmentación de objetos circulares o irregulares.         #    
#                                                           #
# Grupo de investigación:                                   #
# Métodos computacionales en nano-biomateriales y biomedicina
# Dra. Analila Luna Valenzuela (ORCID: 0000-0002-9794-8193) #
# Dr. Isidoro López-Miranda (ORCID: 0009-0000-5654-6756)    #
#                                                           # 
# Versión 10.09, 20250811_112438                            #
#                                                           #
#***********************************************************#**************************************************#
import os                                                   # Manejo de archivos y directorios
import tkinter as tk                                        # Interfaz gráfica
import numpy as np                                          # Manejo de arreglos y matrices
from tkinter import filedialog, messagebox                  # Funciones para abrir diálogos de archivos y mensajes
from tkinter import ttk                                     # Estilos y widgets adicionales
from tkinter import colorchooser                            # Diálogos para seleccionar colores
from tkinter import Menu                                    # Clase para crear menús 
from tkinter import Canvas                                  # Clase para crear lienzos
from tkinter import Label, Entry, Button                    # Widgets de etiquetas, campos de entrada y botones
from tkinter import Scrollbar, Frame                        # Widgets de barra de desplazamiento y marcos
from tkinter import OptionMenu, LabelFrame                  # Widgets de menús desplegables y recuadros con etiquetas
from tkinter import HORIZONTAL, VERTICAL                    # Constantes para orientaciones
from tkinter import RAISED, FLAT, SUNKEN, GROOVE, RIDGE     # Estilos de borde para botones
from tkinter import LEFT, RIGHT, TOP, BOTTOM, BOTH, X, Y    # Constantes de alineación
from tkinter import NW, N, E, W, NE, SE, SW, S, CENTER      # Constantes de alineación específica
from tkinter import NORMAL, DISABLED, ACTIVE                # Constantes para los estados de los widgets
from tkinter import END, INSERT, SEL_FIRST, SEL_LAST, SEL   # Constantes para manipular el cursor y selección
from tkinter import Scale                                   # Clase para crear deslizadores
from PIL import Image, ImageTk                              # Manejo de imágenes
import cv2                                                  # OpenCV para el procesamiento de imágenes
import matplotlib.pyplot as plt                             # Librería para graficar
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg # Clase para mostrar la gráfica en tkinter
from math import sqrt                                       # Función para calcular la raíz cuadrada
import math                                                 # Funciones matemáticas
from statistics import mean, median, stdev                  # Funciones estadísticas
import io                                                   # Entrada/Salida de datos
import time                                                 # Funciones para medir el tiempo
import inspect                                              # Inspección de objetos y funciones
from scipy.stats import norm                                # Funciones estadísticas avanzadas
#***********************************************************#**************************************#
# Variables globales para las coordenadas y la línea actual #
Ancho_img = 600                                             # Ancho de la imagen
Alto_img = 400                                              # Alto de la imagen 
BASE_WIDTH = 800                                            # Ancho base de la ventana
BASE_HEIGHT = 600                                           # Altura base de la ventana
BASE_WIDTH_max = 1024                                       # Ancho máximo de la ventana
BASE_HEIGHT_max = 768                                       # Altura máxima de la ventana
#                                                           #
####################################################################################################
#                                                           #
class Ventana_Usuario_v5_05(tk.Tk):                         # Clase para la ventana principal
    def __init__(self):                                     # Constructor de la clase Ventana_Usuario_v5_05
        super().__init__()                                  # Inicializar la clase madre
        # --------------------------------------------------#
        # Configuración principal de la ventana             #
        self.title("SICS: UAdeO Scientific Image Counting System")     # Título de la ventana
        self.geometry(f"{BASE_WIDTH}x{BASE_HEIGHT}")        # Tamaño de la ventana
        self.protocol("WM_DELETE_WINDOW", self.on_closing)  # Capturar el evento de cierre de la ventana
        #                                                   #
        # --------------------------------------------------#
        # Configuración de imágenes                         #
        self.image_directory = None                         # Directorio de las imágenes
        self.current_image_path = None                      # Ruta de la imagen actual
        self.original_image = None                          # Imagen original sin cambios
        self.resized_image = None                           # Imagen redimensionada
        self.image_refs = []                                # Referencias de las imágenes
        self.image_labels = []                              # Etiquetas de las miniaturas
        self.img_tk = None                                  # Imagen en formato Tkinter
        self.temp_image = None                              # Imagen temporal procesada
        self.temp_image_name = ""                           # Nombre de la imagen temporal
        self.selected_thumbnail_frame = None                # Frame de la miniatura seleccionada
        #                                                   #
        # --------------------------------------------------#
        # Zoom y escala                                     #        
        self.scale_factor = 1.0                             # Zoom actual
        self.min_scale = 0.1                                # Zoom mínimo permitido
        self.max_scale = 5.0                                # Zoom máximo permitido
        #                                                   #
        # Control de arrastre                               #
        self.last_x = 0                                     # Posición X del mouse antes del arrastre
        self.last_y = 0                                     # Posición Y del mouse antes del arrastre
        self.x_offset = 0                                   # centrado
        self.y_offset = 0                                   # centrado
        #                                                   #
        # --------------------------------------------------#
        # Gestión de estado y acciones                      #
        self.is_loading = False                             # Evitar cargas múltiples
        self.image_history = []                             # Historial de cambios
        self.just_undone = False                            # Evitar acciones múltiples
        self.undo_stack = []                                # Cambios realizados
        self.redo_stack = []                                # Cambios deshechos
        self.slider_repeat_job = None                       # Trabajo repetido del slider
        #                                                   #
        # --------------------------------------------------#
        # Configuración de la tabla de datos                #
        self.table_data = {"Número": [], "Conteo": []}      # Datos de la tabla
        self.selected_row = None                            # Fila seleccionada
        self.selected_row_index = None                      # Índice de la fila seleccionada
        self.agregar_a_tabla = False                        # Bandera para agregar a la tabla
        #                                                   #
        # --------------------------------------------------#
        # Variables de medición y dibujo                    #
        self.lines_drawn = []                               # Líneas dibujadas
        self.selected_line = None                           # Línea seleccionada
        self.start_x = self.start_y = 0                     # Coordenadas iniciales
        self.end_x = self.end_y = 0                         # Coordenadas finales
        self.line_id = None                                 # ID de la línea actual
        self.rect_id = None                                 # ID del rectángulo
        self.canvas_x_offset = 0                            # Desplazamiento x del canvas
        self.canvas_y_offset = 0                            # Desplazamiento y del canvas
        self.contour_canvas_ids = []                        # guardar los IDs de los contornos
        self.contour_original_coords = []                   # Guarda info original de 
        self.medicion_lineas = []                           # Coordenadas de las líneas medidas
        self.medicion_rectangulos = []                      # Coordenadas de los rectángulos medidos
        #                                                   #
        # --------------------------------------------------#
        # Variables para el conteo de objetos               #        
        self.manual_annotations = []                        # (x, y, r)
        self.evaluation_canvas_ids = []                     # Objetos visuales para TP, FP, FN
        self.match_threshold = 15                           # Distancia máxima para considerar coincidencia
        #                                                   #
        # --------------------------------------------------#
        # Bandera para medir                                #
        self.is_measuring_reference = False                 # Bandera para medir la referencia
        self.is_measuring_rectangle = False                 # Bandera para medir la referencia
        #                                                   #
        # --------------------------------------------------#
        # Variables relacionadas con la medición de distancia#
        self.MedicionPixeles = 0.0                          # Medición en píxeles
        self.MedicionDistancia = 0.0                        # Medición en distancia
        self.MedicionLongitud = 0.0                         # Medición en longitud
        self.ValorPixel = tk.DoubleVar(value=1.0)           # Valor de píxeles
        self.ValorDistancia = tk.DoubleVar(value=1.0)       # Valor de distancia
        self.ValorLongitud = tk.DoubleVar(value=0.0)        # Valor de longitud
        self.ValorLargo = tk.DoubleVar(value=0.0)           # Valor del largo del rectángulo
        self.ValorAncho = tk.DoubleVar(value=0.0)           # Valor del ancho del rectángulo
        self.ValorConversion = 1.0                          # Valor de conversión
        self.conversion_text = tk.StringVar(value="0.0")    # Texto de conversión
        self.nuevo_limite_maximo = tk.DoubleVar(value=0.0)  # Nuevo límite máximo
        #                                                   #
        # --------------------------------------------------#
        # Valores iniciales paa la medición de contornos    #
        self.min_radius = 10.0                              # Radio mínimo para la detección de contornos
        self.max_radius = 50.0                              # Radio máximo para la detección de contornos
        self.min_dist = 20.0                                # Distancia mínima entre los centros de los círculos detectados     
        #                                                   #
        # --------------------------------------------------#
        # Unidad de medición                                #
        self.distance_units_var = tk.StringVar() #value="unidad_inicial")  # Variable para las unidades de distancia
        self.distance_units_var.set("px")                   # Valor por defecto de las unidades de distancia
        self.distance_units_var.trace_add("write", lambda *args: self.refresh_distance_labels()) #
        #                                                   #
        # --------------------------------------------------#
        # Variables para seleccionar colores                #
        self.current_selection = 'lower'                    # Selección actual
        self.is_selecting_color = False                     # Bandera para selección de color
        self.current_selection = None                       # Selección actual de color
        self.lower_bound = None                             # Límite superior de la selección de color
        self.upper_bound = None                             # Límite superior de la selección de color
        self.temp_color = None                              # Para almacenar el color seleccionado temporalmente        
        #                                                   #
        # --------------------------------------------------#
        # Inicialización de variables globales              #
        self.Ancho_img = Ancho_img                          # Ancho de la imagen
        self.Alto_img = Alto_img                            # Alto de la imagen
        #                                                   #
        # --------------------------------------------------#
        # Variables para la cámara                          #        
        self.camera_active = False                          # Bandera para la cámara
        self.cap = None                                     # Cámara desactivada por defecto
        self.selected_camera_index = None                   # Índice de la cámara seleccionada
        #*************************************************************************************
        #*******        Configuración de la ventana principal       **************************
        #*************************************************************************************
        self.grid_rowconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=15)
        self.grid_columnconfigure(0, weight=1)
        self.grid_columnconfigure(1, weight=12)
        #*************************************************************************************
        #*******            Configuración de los Frames             **************************
        #*************************************************************************************
        # Columna izquierda
        self.left_frame = tk.Frame(self, relief="flat", bd=1, bg=self.cget("bg"))
        self.left_frame.grid(row=0, column=0, sticky="nsew")#
        # Columna derecha
        self.right_frame = tk.Frame(self, relief="flat", bd=1, bg=self.cget("bg"))
        self.right_frame.grid(row=0, column=1, sticky="nsew")
        # Fila inferior que abarca ambas columnas
        self.bottom_frame = tk.Frame(self, relief="flat", bd=1, bg=self.cget("bg"))
        self.bottom_frame.grid(row=1, column=0, columnspan=2, sticky="nsew")
        self.setup_left_frame()
        self.setup_right_frame()
        self.setup_bottom_frame()

    #####################################################################################################
    #                              Imagen de la columna izquierda                                       #
    #####################################################################################################
    def setup_left_frame(self):
        self.main_frame = tk.Frame(self.left_frame, bg=self.cget("bg"))
        self.main_frame.grid(row=0, column=0, padx=5, pady=0, sticky="nsew")
        #***********************************************************************************#
        #              Visualización de imagen                                              #       
        #***********************************************************************************#
        self.button_frame_below_canvas = tk.Frame(self.main_frame)
        self.button_frame_below_canvas.grid(row=1, column=0, pady=0, sticky="ew")
        self.main_frame = tk.Frame(self)
        self.main_frame.grid(row=0, column=0, padx=10, pady=0, sticky="nsew")
        self.canvas_width = Ancho_img
        self.canvas_height = Alto_img
        self.notebook_frame = tk.Frame(self.main_frame)
        self.notebook_frame.grid(row=0, column=0, padx=10, pady=0, sticky="nsew")
        self.notebook_frame.grid_rowconfigure(0, weight=1)
        self.notebook_frame.grid_columnconfigure(0, weight=1)
        self.notebook = ttk.Notebook(self.notebook_frame)
        self.notebook.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")

        #***********************************************************************************#
        #*****************      Pestaña para la imagen temporal     ************************#
        #***********************************************************************************#
        # Pestaña para imagen temporal
        self.canvas_tab = tk.Frame(self.notebook)
        self.notebook.add(self.canvas_tab, text="Imagen temporal")
        self.canvas = tk.Canvas(self.canvas_tab, bg="gray", width=self.canvas_width, height=self.canvas_height)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.v_scrollbar = tk.Scrollbar(self.canvas_tab, orient=tk.VERTICAL, command=self.canvas.yview)
        self.v_scrollbar.grid(row=0, column=1, sticky="ns")
        self.h_scrollbar = tk.Scrollbar(self.canvas_tab, orient=tk.HORIZONTAL, command=self.canvas.xview)
        self.h_scrollbar.grid(row=1, column=0, sticky="ew")
        self.canvas.config(yscrollcommand=self.v_scrollbar.set, xscrollcommand=self.h_scrollbar.set)
        self.canvas.bind("<Button-1>", self.handle_color_selection)

        #***********************************************************************************#
        #*****************      Pestaña para imagen original          **********************#
        #***********************************************************************************# 
        self.canvas_tab_temp = tk.Frame(self.notebook, relief="flat")
        self.notebook.add(self.canvas_tab_temp, text="Imagen original")
        self.canvas_temp = tk.Canvas(self.canvas_tab_temp, bg="gray", width=self.canvas_width, height=self.canvas_height)
        self.canvas_temp.grid(row=0, column=0, sticky="nsew")
        self.v_scrollbar_temp = tk.Scrollbar(self.canvas_tab_temp, orient=tk.VERTICAL, command=self.canvas_temp.yview)
        self.v_scrollbar_temp.grid(row=0, column=1, sticky="ns")
        self.h_scrollbar_temp = tk.Scrollbar(self.canvas_tab_temp, orient=tk.HORIZONTAL, command=self.canvas_temp.xview)
        self.h_scrollbar_temp.grid(row=1, column=0, sticky="ew")
        self.canvas_temp.config(yscrollcommand=self.v_scrollbar_temp.set, xscrollcommand=self.h_scrollbar_temp.set)
        #                                                                                   #
        #***********************************************************************************#
        #********************          Pestaña para resultados          ********************#
        #***********************************************************************************#
        # Configuración de la pestaña "Resultados"
        self.canvas_tab_results = tk.Frame(self.notebook, relief="flat")  
        self.notebook.add(self.canvas_tab_results, text="Resultados")
        self.results_canvas = tk.Canvas(self.canvas_tab_results, bg=self.cget("bg"))
        self.results_canvas.grid(row=0, column=0, sticky="nsew")
        self.results_frame = tk.Frame(self.results_canvas, bg=self.cget("bg"))
        self.results_canvas.create_window((0, 0), window=self.results_frame, anchor="nw")

        # Configuración de grid para la pestaña "Resultados"
        self.canvas_tab_results.grid_rowconfigure(0, weight=1)
        self.canvas_tab_results.grid_columnconfigure(0, weight=1)
        self.results_frame.grid_columnconfigure(0, weight=0, minsize=150)
        self.results_frame.grid_columnconfigure(1, weight=0, minsize=250)
        self.results_frame.grid_rowconfigure(0, weight=0, minsize=300)
        self.table_frame = tk.Frame(self.results_frame, bg=self.cget("bg"))
        self.table_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)

        # Configuración de la tabla
        self.results_table = ttk.Treeview(
            self.table_frame,
            columns=("Medicion", "Diámetro"),
            show="headings",
            height=18,
        )
        self.results_table.grid(row=0, column=0, sticky="nsew")
        self.results_table.heading("Medicion", text="Medición")
        self.results_table.heading("Diámetro", text="Diámetro")
        self.results_table.column("Medicion", width=80, anchor="center")
        self.results_table.column("Diámetro", width=80, anchor="center")

        # Barras de desplazamiento para la tabla
        self.v_scrollbar_table = tk.Scrollbar(self.table_frame, orient=tk.VERTICAL, command=self.results_table.yview)
        self.v_scrollbar_table.grid(row=0, column=1, sticky="ns")
        self.results_table.config(yscrollcommand=self.v_scrollbar_table.set)

        # Función para limpiar la tabla
        def clear_table():
            for item in self.results_table.get_children():
                self.results_table.delete(item)
            for widget in self.hist_canvas.winfo_children():
                widget.destroy()
            for widget in self.stats_frame.winfo_children():
                widget.destroy()

        def export_data():
            file_path = tk.filedialog.asksaveasfilename(defaultextension=".dat", filetypes=[("Archivos .dat", "*.dat")])
            if not file_path:
                return
            with open(file_path, "w") as file:
                file.write("Medicion\tDiámetro\n")
                for row in self.results_table.get_children():
                    row_values = self.results_table.item(row, "values")
                    file.write("\t".join(row_values) + "\n")
            tk.messagebox.showinfo("Exportación exitosa", "Los datos se han exportado correctamente.")

        def delete_row():
            selected_item = self.results_table.selection()
            if selected_item:
                self.results_table.delete(selected_item)
                for idx, item in enumerate(self.results_table.get_children(), start=1):
                    current_values = self.results_table.item(item, "values")
                    self.results_table.item(item, values=(idx, current_values[1]))
            else:
                messagebox.showwarning("Advertencia", "Seleccione una fila para eliminar.")

        def show_context_menu(event):
            if hasattr(self, "context_menu") and self.context_menu:
                self.context_menu.destroy()
            self.context_menu = tk.Menu(self.results_table, tearoff=0)
            self.context_menu.add_command(label="Eliminar fila", command=delete_row)
            self.context_menu.post(event.x_root, event.y_root)
            self.results_table.bind("<Button-1>", hide_context_menu)
        def hide_context_menu(event=None):
            if hasattr(self, "context_menu") and self.context_menu:
                self.context_menu.destroy()
                self.context_menu = None
            self.results_table.unbind("<Button-1>")
        self.results_table.bind("<Button-3>", show_context_menu)
        self.results_table.bind("<Delete>", lambda event: delete_row())

        # Frame derecho (Columna derecha)
        self.right_frame = tk.Frame(self.results_frame, bg=self.cget("bg"))
        self.right_frame.grid(row=0, column=1, sticky="nsew", padx=5, pady=2)
        self.right_frame.grid_propagate(True)

        self.right_top_frame = tk.Frame(
            self.right_frame,
            bg="white",
            relief="groove",
            borderwidth=1,
            width=250,
            height=220
        )
        self.right_top_frame.grid(row=0, column=0, padx=5, pady=2)
        self.right_top_frame.grid_propagate(False)

        self.hist_canvas = tk.Canvas(
            self.right_top_frame,
            bg="white",
            width=250,
            height=220
        )
        self.hist_canvas.pack(fill="both", expand=False)

        self.right_bottom_frame = tk.Frame(
            self.right_frame,
            bg="white",
            relief="groove",
            borderwidth=1,
            width=250,
            height=100
        )
        self.right_bottom_frame.grid(row=1, column=0, padx=5, pady=2)
        self.right_bottom_frame.grid_propagate(False)

        self.stats_frame = tk.Frame(
            self.right_bottom_frame,
            bg="white",
            width=300,
            height=100
        )
        self.stats_frame.pack(fill="both", expand=True, padx=5, pady=5)

        tk.Label(
            self.right_bottom_frame,
            text="Intervalos:",
            font=("Arial", 9),
            bg="white"
        ).pack(side="left", padx=5)

        self.entry_bins = tk.Entry(self.right_bottom_frame, width=5)
        self.entry_bins.insert(0, "10")
        self.entry_bins.pack(side="left")
        self.entry_bins.bind("<Return>", lambda event: self.update_histogram_from_entry())
        self.entry_bins.bind("<FocusOut>", lambda event: self.update_histogram_from_entry())

        # Configuración de Canvas para ajustarse al contenido
        def configure_canvas(event):
            self.results_canvas.configure(scrollregion=self.results_canvas.bbox("all"))
        self.results_frame.bind("<Configure>", configure_canvas)

        #************************************************************************************#
        #********************          Pestaña para la cámara           *********************#
        #************************************************************************************#
        self.camera_tab = tk.Frame(self.notebook, relief="flat")
        self.notebook.add(self.camera_tab, text="Cámara")
        self.camera_canvas = tk.Canvas(self.camera_tab, bg="gray", width=self.canvas_width, height=self.canvas_height)
        self.camera_canvas.grid(row=0, column=0, sticky="nsew")

        # Nuevo Frame para los botones debajo del Notebook
        self.button_frame_below_canvas = tk.Frame(self.main_frame)
        self.button_frame_below_canvas.grid(row=1, column=0, pady=0, sticky="ew")

        btn_load_images = tk.Button(self.button_frame_below_canvas, text="Directorio", command=self.load_images)
        btn_load_images.pack(side=tk.LEFT, padx=5, pady=0)
        btn_refresh_images = tk.Button(self.button_frame_below_canvas, text="Actualizar", command=self.refresh_images)
        btn_refresh_images.pack(side=tk.LEFT, padx=0, pady=0)
        btn_save = tk.Button(self.button_frame_below_canvas, text="Guardar imagen", command=self.save_image)
        btn_save.pack(side=tk.LEFT, padx=0, pady=0)
        btn_clear_table = tk.Button(self.button_frame_below_canvas, text="Limpiar tabla", command=clear_table)
        btn_clear_table.pack(side=tk.LEFT, padx=0, pady=0)
        btn_export_data = tk.Button(self.button_frame_below_canvas, text="Exportar datos", command=export_data)
        btn_export_data.pack(side=tk.LEFT, padx=0, pady=0)
        self.calculate_stats_button = tk.Button(self.button_frame_below_canvas, text="Gráfica", command=lambda: self.calculate_statistics(self.get_table_values()))
        self.calculate_stats_button.pack(side="left", padx=0, pady=0)
    #####################################################################################################
    #                              Botones de la columna derecha                                        #
    #####################################################################################################
    def setup_right_frame(self):
        frame_top = tk.Frame(self.right_frame, bg=self.cget("bg"))
        frame_top.grid(row=0, column=0, padx=5, pady=5, sticky="w")
        self.right_frame.grid_rowconfigure(0, weight=0)
        self.right_frame.grid_columnconfigure(0, weight=1)

        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #                       Columna Derecha: Fila 1                                 #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#        
        self.button_frame = tk.Frame(self.main_frame)
        self.button_frame.grid(row=0, column=2, sticky="n")

        self.button_frame_top = tk.Frame(self.button_frame) 
        self.button_frame_top.pack(side=tk.TOP, padx=2, pady=0, anchor="n")
        self.button_frame_middle = tk.Frame(self.button_frame)
        self.button_frame_middle.pack(side=tk.TOP, padx=2, pady=2, anchor="n")
        self.button_frame_bottom = tk.Frame(self.button_frame)
        self.button_frame_bottom.pack(side=tk.TOP, padx=2, pady=2, anchor="n")

	    ###################################################################################
        ##################               Fila 1 de botones        #########################
	    ###################################################################################
        # Frame para la fila 1
        self.button_row_1 = tk.Frame(self.button_frame_bottom)
        self.button_row_1.pack(side=tk.TOP, anchor="w", pady=0)  # Reduce el margen vertical
        zoom_in_button = tk.Button(self.button_row_1, text="Zoom +", command=self.zoom_in)
        zoom_in_button.pack(side=tk.LEFT, padx=4, pady=2)
        zoom_out_button = tk.Button(self.button_row_1, text="Zoom -", command=self.zoom_out)
        zoom_out_button.pack(side=tk.LEFT, padx=4, pady=2)
        btn_undo = tk.Button(self.button_row_1, text="Deshacer", command=self.undo_change)
        btn_undo.pack(side=tk.LEFT, padx=4, pady=2)
        btn_redo = tk.Button(self.button_row_1, text="Rehacer", command=self.redo_change)
        btn_redo.pack(side=tk.LEFT, padx=4, pady=2)
        self.toggle_button = tk.Menubutton(self.button_row_1, text="Cámara", relief="raised", direction="below")
        self.toggle_button.pack(side=tk.LEFT, padx=4, pady=2)
        self.menu = tk.Menu(self.toggle_button, tearoff=0)
        self.toggle_button.config(menu=self.menu)
        self.menu.add_command(label="Buscar cámaras", command=self.search_cameras)
        btn_take_photo = tk.Button(self.button_row_1, text="Tomar Foto", command=self.take_photo)
        btn_take_photo.pack(side=tk.LEFT, padx=4, pady=2)
        btn_ayuda_usuario = tk.Button(self.button_row_1, text="Ayuda", command=self.ayuda_usuario)
        btn_ayuda_usuario.pack(side=tk.LEFT, padx=4, pady=2)
        #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #                       Parámetros de referencia                                #
        #                       Columna Derecha: Fila 2                                 #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        self.button_row_4 = tk.Frame(self.button_frame_bottom)
        self.button_row_4.pack(side=tk.TOP, anchor="w")

        contour_frame = tk.LabelFrame(
            self.button_row_4,
            text="Parámetros de referencia",
            padx=0,
            pady=0,
            labelanchor="nw",
            width=630,
            height=110,
            font=("Arial", 10)
        )
        contour_frame.pack_propagate(False)
        contour_frame.pack(side=tk.TOP, anchor="w", padx=5, pady=0)

        self.selected_shape = tk.StringVar(value="")
        vcmd = (self.register(self.validar_numero), '%P')

        # Función para actualizar las etiquetas de unidades
        def update_labels(new_unit):
            self.lengthLine_unit_label.config(text=new_unit)
            self.unidadesConversion_label.config(text=f"{new_unit}/px")

        reference_frame = tk.Frame(contour_frame)
        reference_frame.pack(side=tk.TOP, fill=tk.X, padx=0, pady=0)

        # Variables para almacenar los valores de pixeles y distancia
        self.pixels = 0
        self.distance = 0
        self.reference = 0
        self.measure_reference = 0
        self.ValorPixel = tk.DoubleVar(value=0.0)
        self.ValorDistancia = tk.DoubleVar(value=0.0)
        self.ValorLongitud = tk.DoubleVar(value=0.0)
        self.ValorLargo = tk.DoubleVar(value=0.0)
        self.ValorAncho = tk.DoubleVar(value=0.0)

        # Guardar referencias de botones
        self.button_states = {
              "measure_reference": False,
              "pixels": False,
              "distance": False,
              "reference": False,
              "lengthLine": False,
              }

        # Función para manejar la selección de los botones
        def toggle_button(button_type):
            """Activa/desactiva los botones y cambia el color."""
            if button_type == "measure_reference":
                if self.button_states["measure_reference"]:
                    measure_reference_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["measure_reference"] = False
                    self.pixels_entry.config(state=tk.NORMAL)
                    self.distance_entry.config(state=tk.NORMAL)
                    self.pixels_button.config(bg="lightgray", relief=tk.RAISED)
                    self.distance_button.config(bg="lightgray", relief=tk.RAISED)
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["lengthLine"] = False
                    self.canvas.unbind("<ButtonPress-1>")
                    self.canvas.unbind("<B1-Motion>")
                    self.canvas.unbind("<ButtonRelease-1>")
                    self.is_measuring_reference = False
                else:
                    measure_reference_button.config(relief=tk.SUNKEN, bg="lightgreen")
                    self.button_states["measure_reference"] = True
                    self.pixels_button.config(relief=tk.RAISED, bg="lightgray", state=tk.NORMAL)
                    self.button_states["pixels"] = False
                    self.pixels_entry.config(state=tk.NORMAL)
                    self.distance_button.config(relief=tk.RAISED, bg="lightgray", state=tk.NORMAL)
                    self.button_states["distance"] = False
                    self.distance_entry.config(state=tk.NORMAL)
                    use_reference_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["reference"] = False
                    self.canvas.bind("<ButtonPress-1>", self.start_line)
                    self.canvas.bind("<B1-Motion>", self.draw_line)
                    self.canvas.bind("<ButtonRelease-1>", self.finish_line)
                    self.is_measuring_reference = True
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["lengthLine"] = False
                    self.lengthLine_entry.config(state=tk.DISABLED)
            elif button_type == "pixels":
                if self.button_states["pixels"]:
                    self.pixels_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["pixels"] = False
                    self.pixels_entry.config(state=tk.NORMAL)
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["lengthLine"] = False
                    use_reference_button.config(relief=tk.RAISED, bg="lightgray")
                    self.lengthLine_entry.config(state=tk.DISABLED)
                else:
                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
                    self.button_states["pixels"] = True
                    self.pixels_entry.config(state=tk.DISABLED)
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["lengthLine"] = False
                    self.lengthLine_entry.config(state=tk.DISABLED)
                    self.canvas.unbind("<ButtonPress-1>")
                    self.canvas.unbind("<B1-Motion>")
                    self.canvas.unbind("<ButtonRelease-1>")
            elif button_type == "distance":
                if self.button_states["distance"]:
                    self.distance_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["distance"] = False
                    self.distance_entry.config(state=tk.NORMAL)
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["lengthLine"] = False
                    self.use_reference_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["reference"] = True
                    self.lengthLine_entry.config(state=tk.DISABLED)
                else:
                   self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")
                   self.button_states["distance"] = True
                   self.distance_entry.config(state=tk.DISABLED)
                   self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
                   self.button_states["pixels"] = True
                   self.pixels_entry.config(state=tk.DISABLED)
                   self.lengthLine_entry.config(state=tk.DISABLED)
                   self.canvas.unbind("<ButtonPress-1>")
                   self.canvas.unbind("<B1-Motion>")
                   self.canvas.unbind("<ButtonRelease-1>")
            elif button_type == "reference":
                if self.button_states["reference"]:
                    use_reference_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["reference"] = False
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["lengthLine"] = False
                    self.lengthLine_entry.config(state=tk.DISABLED)
                else:
                    use_reference_button.config(relief=tk.SUNKEN, bg="lightcoral")
                    self.button_states["reference"] = True
                    measure_reference_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["measure_reference"] = False
                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
                    self.button_states["pixels"] = False
                    self.pixels_entry.config(state=tk.DISABLED)
                    self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")
                    self.distance_entry.config(state=tk.DISABLED)
                    self.canvas.unbind("<ButtonPress-1>")
                    self.canvas.unbind("<B1-Motion>")
                    self.canvas.unbind("<ButtonRelease-1>")
                    self.is_measuring_reference = False
                    self.lengthLine_entry.config(state=tk.DISABLED)
            elif button_type == "lengthLine":
                if self.button_states["lengthLine"]:
                    use_reference_button.config(relief=tk.SUNKEN, bg="lightcoral")
                    self.button_states["reference"] = True
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["lengthLine"] = False
                    self.lengthLine_entry.config(state=tk.DISABLED)
                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
                    self.pixels_entry.config(state=tk.DISABLED)
                    self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")
                    self.distance_entry.config(state=tk.DISABLED)
                    self.lengthLine_entry.config(state=tk.DISABLED)

                    self.canvas.unbind("<ButtonPress-1>")
                    self.canvas.unbind("<B1-Motion>")
                    self.canvas.unbind("<ButtonRelease-1>")
                    self.is_measuring_reference = False
                else:
                    use_reference_button.config(relief=tk.SUNKEN, bg="lightcoral")
                    self.button_states["reference"] = True
                    measure_reference_button.config(relief=tk.RAISED, bg="lightgray")
                    self.button_states["measure_reference"] = False

                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgray")
                    self.button_states["pixels"] = False
                    self.pixels_entry.config(state=tk.DISABLED)
                    self.distance_button.config(relief=tk.SUNKEN, bg="lightgray")
                    self.button_states["distance"] = False 
                    self.distance_entry.config(state=tk.DISABLED)

                    self.use_lengthLine_button.config(relief=tk.SUNKEN, bg="lightgreen")
                    self.button_states["lengthLine"] = True
                    self.lengthLine_entry.config(state=tk.NORMAL)
                    self.canvas.bind("<ButtonPress-1>", self.start_line)
                    self.canvas.bind("<B1-Motion>", self.draw_line)
                    self.canvas.bind("<ButtonRelease-1>", self.finish_line)
                    self.is_measuring_reference = True

        # Función para medir la referencia (habilitar dibujo)
        def measure_reference():
            toggle_button("measure_reference")
        measure_reference_button = tk.Button(reference_frame,
                                     text="Medir\nreferencia",
                                     command=lambda: toggle_button("measure_reference"),
                                     relief=tk.RAISED,
                                     activebackground="lightgray",
                                     activeforeground="black",
                                     )
        measure_reference_button.pack(side=tk.LEFT, padx=5)

        # Botón "Pixeles"
        def use_pixels():
            print("Pixeles utilizados.")
            toggle_button("pixels")

        self.pixels_button = tk.Button(
            reference_frame,
            text="Pixeles",
            bg="lightgray",
            command=lambda: toggle_button("pixels"),
            relief=tk.RAISED,
            activebackground="lightgray",
            activeforeground="black"
        )
        self.pixels_button.pack(side=tk.LEFT, padx=5)
        self.pixels_entry = tk.Entry(reference_frame, width=7, textvariable=self.ValorPixel, validate="key", validatecommand=vcmd)
        self.pixels_entry.pack(side=tk.LEFT, padx=0)
        self.pixels_entry.delete(0, tk.END)
        self.pixels_entry.insert(0, "0.0")

        self.pixels_entry.bind("<FocusOut>", self.validar_y_actualizar)

        self.pixels_entry.bind("<Return>", lambda event: (
            self.validar_y_actualizar(),
            self.realizar_calculo(),
            self.toggle_estado_boton("pixels")
        ))

        # Símbolo "=" entre Pixeles y Distancia conocida
        equal_button = tk.Label(reference_frame, text="=", anchor="w")
        equal_button.pack(side=tk.LEFT, padx=0)

        # Botón "Distancia conocida"
        def use_lengthLine():
            print("Longitud utilizada.")
            toggle_button("length")
        self.distance_button = tk.Button(
            reference_frame,
            text="Referencia",
            bg="lightgray",
            command=lambda: toggle_button("distance"),
            relief=tk.RAISED,
            activebackground="lightgray",
            activeforeground="black"
        )
        self.distance_button.pack(side=tk.LEFT, padx=5)

        self.distance_entry = tk.Entry(reference_frame, width=7, textvariable=self.ValorDistancia, validate="key", validatecommand=vcmd)
        self.distance_entry.pack(side=tk.LEFT, padx=10)

        self.distance_entry.delete(0, tk.END)
        self.distance_entry.insert(0, "0.0")

        self.distance_entry.bind("<FocusOut>", self.validar_y_actualizar)

        self.distance_entry.bind("<Return>", lambda event: (
            self.validar_y_actualizar(),
            self.realizar_calculo(),
            self.toggle_estado_boton("distance")
        ))

        self.distance_units_var = tk.StringVar(value="px")
        self.distance_units_menu = tk.OptionMenu(reference_frame,
                                          self.distance_units_var,
                   "px", "nm", "\u03bcm", "mm", "cm", "m",
                                            command=update_labels
                                            )
        self.distance_units_menu.config(width=3)
        self.distance_units_menu.pack(side=tk.LEFT, padx=5)
        radio_text = f"({self.distance_units_var.get()})"

        # Botón "Utilizar referencia" actualizado
        def use_reference():
            toggle_button("reference")
            self.realizar_calculo()
        use_reference_button = tk.Button(reference_frame,
                                         text="Aplicar",
                                         command=use_reference,
                                         relief=tk.RAISED,
                                         activebackground="lightgray",
                                         activeforeground="black",
                                        )
        use_reference_button.pack(side=tk.LEFT, padx=10)
        self.lengthLine_frame = tk.Frame(contour_frame)
        self.lengthLine_frame.pack(side=tk.LEFT, padx=5, pady=0)

        # Botón "Longitud"
        def use_lengthLine():
            toggle_button("lengthLine")
        self.use_lengthLine_button = tk.Button(
            self.lengthLine_frame,
            text="Longitud",
            command=lambda: toggle_button("lengthLine"),
            relief=tk.RAISED,
            activebackground="lightgray",
            activeforeground="black"
        )
        self.use_lengthLine_button.pack(side=tk.LEFT, padx=5)

        self.lengthLine_entry = tk.Entry(self.lengthLine_frame, width=7, textvariable=self.ValorLongitud, validate="key", validatecommand=vcmd)
        self.lengthLine_entry.pack(side=tk.LEFT, padx=0)

        self.lengthLine_entry.delete(0, tk.END)
        self.lengthLine_entry.insert(0, "0.0")
        self.lengthLine_entry.bind("<FocusOut>", self.validar_y_actualizar)
        self.lengthLine_entry.bind("<Return>", self.validar_y_calcular)

        self.lengthLine_unit_label = tk.Label(self.lengthLine_frame, text=self.distance_units_var.get(), anchor="w", width=3)
        self.lengthLine_unit_label.pack(side=tk.LEFT, padx=3)

        # Botón toggle para agregar mediciones a la tabla automáticamente
        self.agregar_a_tabla = False
        agregar_button = tk.Button(
            self.lengthLine_frame,
            text="Agregar a la tabla",
            relief=tk.RAISED,
            width=15
        )
        default_bg = agregar_button.cget("background")
        agregar_button.pack(side=tk.LEFT, padx=5)

        # Función para actualizar tooltip (externo al toggle)
        def actualizar_tooltip_agregar():
            if self.agregar_a_tabla:
                self.agregar_tooltip(agregar_button, "Modo activo:\nSe agregará automáticamente\na la tabla la medición de 'Longitud'")
            else:
                self.agregar_tooltip(agregar_button, "Presiona para agregar la medición de\n'Longitud' a la tabla")

        # Función para alternar el estado del botón
        def toggle_agregar_a_tabla():
            self.agregar_a_tabla = not self.agregar_a_tabla
            if self.agregar_a_tabla:
                agregar_button.config(relief=tk.SUNKEN, bg="lightblue", text="Guardando")
            else:
                agregar_button.config(relief=tk.RAISED, bg=default_bg, text="Agregar a la tabla")
            actualizar_tooltip_agregar()
        agregar_button.config(command=toggle_agregar_a_tabla)
        actualizar_tooltip_agregar()

        tk.Label(contour_frame, text="  ").pack(side=tk.LEFT, padx=10)

        self.rectangle_frame = tk.Frame(contour_frame)
        self.rectangle_frame.pack(side=tk.LEFT, padx=5, pady=0)

        self.reset_button = tk.Button(self.rectangle_frame, text="Reiniciar valores", command=self.reset_measurement, width=11)
        self.reset_button.pack(side=tk.LEFT, padx=5, pady=1)

        self.conversion_frame = tk.Frame(self.rectangle_frame, relief=tk.GROOVE, bd=2, padx=5, pady=5)
        self.conversion_frame.pack(side=tk.LEFT, padx=5, pady=0)

        self.conversion_label = tk.Label(self.conversion_frame, text="0.0", anchor="w")
        self.conversion_label.pack(side=tk.LEFT, padx=5)

        self.unidadesConversion_label = tk.Label(self.conversion_frame, text=self.distance_units_var.get() + "/px", anchor="w", width=6)
        self.unidadesConversion_label.pack(side=tk.LEFT, padx=5)
        #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #                       Procesamiento de imágenes                               #
        #                       Columna Derecha: Fila 3                                 #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #
        ###################################################################################
        ##########      Agrupación en Contorno 2da y 3ra fila de botones       ############
        ###################################################################################
        # Frame para agrupar las filas
        Frame_Proceso_Imagen = tk.LabelFrame(
            self.button_frame_bottom,
            text="Procesamiento de Imagen",
            padx=10,
            pady=0,
            labelanchor="nw",
            width=630,
            height=140,
            font=("Arial", 10)
        )
        Frame_Proceso_Imagen.pack_propagate(False)  # Deshabilitar la redimensión automática
        Frame_Proceso_Imagen.pack(side=tk.TOP, anchor="w", padx=5, pady=0)

        #####################################################################################
        #       Configuración de las columas y filas dentro del Frame_Proceso_Imagen        #
        ########********************************************************************#########
        contenedor_columnas = tk.Frame(Frame_Proceso_Imagen)
        contenedor_columnas.pack(fill="x", expand=True)

        col_izquierda = tk.Frame(contenedor_columnas, width=460, height=140)
        col_izquierda.pack_propagate(False)
        col_izquierda.pack(side=tk.LEFT, padx=5, pady=5)

        col_derecha = tk.Frame(contenedor_columnas, width=170, height=140)
        col_derecha.pack_propagate(False)
        col_derecha.pack(side=tk.LEFT, padx=5, pady=5)

        fila_superior = tk.Frame(col_izquierda)
        fila_superior.pack(side=tk.TOP, pady=(0, 5), anchor="w")

        btn_reset = tk.Button(fila_superior, text="Reiniciar\nimagen", command=self.reset_image)
        btn_reset.pack(side=tk.LEFT, padx=(0, 5))

        tk.Label(fila_superior, text="  ").pack(side=tk.LEFT, padx=5)

        frame_slider_hist = tk.Frame(fila_superior)
        frame_slider_hist.pack(side=tk.LEFT, padx=(0, 5))
        tk.Label(frame_slider_hist, text="Intensidad").pack(side=tk.TOP)
        self.equalize_value_label = tk.Label(frame_slider_hist, text="0", font=("Arial", 9))
        self.equalize_value_label.pack(side=tk.TOP)
        slider_band_hist = tk.Frame(frame_slider_hist)
        slider_band_hist.pack(side=tk.TOP)

        btn_hist_minus = tk.Canvas(slider_band_hist, width=16, height=15, highlightthickness=0, bd=0)
        btn_hist_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_hist_minus_btn = tk.Button(btn_hist_minus, text="\u25C0", fg="#696969", bg="#A9A9A9",
                               activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                               font=("Arial", 9), width=2, padx=0,
                               command=lambda: self.adjust_slider(self.slider_equalize_hist, -1, self.update_equalize_hist))
        btn_hist_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_equalize_hist, -1, self.update_equalize_hist))
        btn_hist_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_hist_minus.create_window(8, 7, window=btn_hist_minus_btn, anchor="center")

        self.slider_equalize_hist = tk.Scale(slider_band_hist, from_=0, to=100, orient=tk.HORIZONTAL,
                                     command=self.update_equalize_hist, sliderlength=20, width=15,
                                     showvalue=False, length=60, highlightthickness=0, borderwidth=1,
                                     troughcolor="#A9A9A9")
        self.slider_equalize_hist.set(0)
        self.slider_equalize_hist.pack(side=tk.LEFT)
        self.bind_slider_trough(self.slider_equalize_hist, self.update_equalize_hist)
        btn_hist_plus = tk.Canvas(slider_band_hist, width=16, height=15, highlightthickness=0, bd=0)
        btn_hist_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_hist_plus_btn = tk.Button(btn_hist_plus, text="\u25B6", fg="#696969", bg="#A9A9A9",
                              activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                              font=("Arial", 9), width=2, padx=0,
                              command=lambda: self.adjust_slider(self.slider_equalize_hist, +1, self.update_equalize_hist))
        btn_hist_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_equalize_hist, +1, self.update_equalize_hist))
        btn_hist_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_hist_plus.create_window(8, 7, window=btn_hist_plus_btn, anchor="center")
        tk.Label(fila_superior, text="  ").pack(side=tk.LEFT, padx=10)
        frame_slider_contrast = tk.Frame(fila_superior)
        frame_slider_contrast.pack(side=tk.LEFT, padx=(0, 5))
        tk.Label(frame_slider_contrast, text="Contraste").pack(side=tk.TOP)
        self.contrast_value_label = tk.Label(frame_slider_contrast, text="0", font=("Arial", 9))
        self.contrast_value_label.pack(side=tk.TOP)
        slider_band_contrast = tk.Frame(frame_slider_contrast)
        slider_band_contrast.pack(side=tk.TOP)
        btn_contrast_minus = tk.Canvas(slider_band_contrast, width=16, height=15, highlightthickness=0, bd=0)
        btn_contrast_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_contrast_minus_btn = tk.Button(btn_contrast_minus, text="\u25C0", fg="#696969", bg="#A9A9A9",
                                   activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                                   font=("Arial", 9), width=2, padx=0,
                                   command=lambda: self.adjust_slider(self.slider_contrast, -1, self.update_contrast))
        btn_contrast_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_contrast, -1, self.update_contrast))
        btn_contrast_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_contrast_minus.create_window(8, 7, window=btn_contrast_minus_btn, anchor="center")
        self.slider_contrast = tk.Scale(slider_band_contrast, from_=-100, to=100, orient=tk.HORIZONTAL,
                                command=self.update_contrast, sliderlength=20, width=15,
                                showvalue=False, length=60, highlightthickness=0, borderwidth=1,
                                troughcolor="#A9A9A9")
        self.slider_contrast.set(0)
        self.slider_contrast.pack(side=tk.LEFT)
        self.bind_slider_trough(self.slider_contrast, self.update_contrast)
        btn_contrast_plus = tk.Canvas(slider_band_contrast, width=16, height=15, highlightthickness=0, bd=0)
        btn_contrast_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_contrast_plus_btn = tk.Button(btn_contrast_plus, text="\u25B6", fg="#696969", bg="#A9A9A9",
                                  activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                                  font=("Arial", 9), width=2, padx=0,
                                  command=lambda: self.adjust_slider(self.slider_contrast, +1, self.update_contrast))
        btn_contrast_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_contrast, +1, self.update_contrast))
        btn_contrast_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_contrast_plus.create_window(8, 7, window=btn_contrast_plus_btn, anchor="center")
        tk.Label(fila_superior, text="  ").pack(side=tk.LEFT, padx=5)
        contenedor_patron_marcar = tk.Frame(fila_superior)
        contenedor_patron_marcar.pack(side=tk.LEFT, padx=5, pady=0)
        self.btn_marcar = tk.Button(contenedor_patron_marcar, text="Seleccionar", height=1, command=self.iniciar_marcado_manual)
        self.btn_marcar.pack(side=tk.TOP, anchor='n', pady=0)
        self.agregar_tooltip(self.btn_marcar, "Presiona para dibujar un patrón sobre\nla imagen. Después presione 'Buscar'")
        self.btn_buscar = tk.Button(contenedor_patron_marcar, text="Buscar", height=1, command=self.detectar_por_patrón_manual, state=tk.DISABLED)
        self.btn_buscar.pack(side=tk.TOP, anchor='n', pady=0)
        fila_inferior = tk.Frame(col_izquierda)
        fila_inferior.pack(side=tk.TOP, pady=(5, 0), anchor="w")
        btn_invert_colors = tk.Button(fila_inferior, text="Invertir color", command=self.invert_colors)
        btn_invert_colors.pack(side=tk.LEFT, padx=20)
        btn_gray_scale = tk.Button(fila_inferior, text="Imagen gris", command=self.convert_to_grayscale)
        btn_gray_scale.pack(side=tk.LEFT, padx=15)
        btn_otsu = tk.Button(fila_inferior, text="Imagen binaria", command=self.apply_otsu_threshold)
        btn_otsu.pack(side=tk.LEFT, padx=15)
        frame_segmentacion = tk.Frame(col_derecha)
        frame_segmentacion.pack(side=tk.TOP, pady=(0, 2)) 
        tk.Label(frame_segmentacion, text="Segmentar imagen").pack(side=tk.TOP)
        self.segment_menu_button = tk.Menubutton(
            frame_segmentacion,
            text="Segmentar color \u25BC",
            relief=tk.RAISED,
            direction="below",
            width=28,
            font=("Arial", 10),
            height=1
        )
        self.segment_menu_button.pack(side=tk.TOP, pady=(2, 5))
        self.segment_menu = tk.Menu(self.segment_menu_button, tearoff=0)
        self.segment_menu_button.config(menu=self.segment_menu)
        self.segment_menu.add_command(label="Segmentar x color", command=self.iniciar_color_segmentacion)
        self.segment_menu.add_command(label="Separar objetos", command=self.iniciar_watershed_segmentacion)
        self.segment_menu.add_command(label="Colores similares", command=self.preparar_kmeans)
        self.frame_k_entry = tk.Frame(frame_segmentacion)
        self.k_label = tk.Label(self.frame_k_entry, text="K:")
        self.k_entry = tk.Entry(self.frame_k_entry, width=3)
        self.k_entry.insert(0, "2")
        self.k_entry.config(state="disabled")
        self.k_entry.bind("<Return>", self.on_enter_k)
        self.k_label.pack(side=tk.LEFT, padx=(0, 2))
        self.k_entry.pack(side=tk.LEFT)
        self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
        self.frame_k_entry.pack_forget()
        self.k_hint_label = tk.Label(
            frame_segmentacion,
            text="Número de colores \n para segmentar",
            font=("Arial", 8),
            fg="gray25"
        )
        self.k_hint_label.pack(side=tk.TOP)
        self.k_hint_label.pack_forget()
        self.color_buttons_frame = tk.Frame(frame_segmentacion)
        self.color1_button = tk.Button(
            self.color_buttons_frame,
            text="Color 1",
            state=tk.DISABLED,
            command=self.confirm_color1,
            width=6,
            height=1,
            font=("Arial", 8),
            relief=tk.SUNKEN
        )
        self.color1_button.pack(side=tk.LEFT, padx=2)
        self.color2_button = tk.Button(
            self.color_buttons_frame,
            text="Color 2",
            state=tk.DISABLED,
            command=self.confirm_color2,
            width=6,
            height=1,
            font=("Arial", 8),
            relief=tk.SUNKEN
        )
        self.color2_button.pack(side=tk.LEFT, padx=2)
        self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
        self.color_buttons_frame.pack_forget()
        self.color_hint_label = tk.Label(
            frame_segmentacion,
            text="Seleccione un color\ny presione el botón",
            font=("Arial", 8),
            fg="gray25"
        )
        self.color_hint_label.pack(side=tk.TOP, pady=(2, 0))
        self.color_hint_label.pack_forget()
        #
        ###################################################################################
        #*********              FRAME: Parámetros de contorno                **************
        ###################################################################################
        Frame_Parametros_Contorno = tk.LabelFrame(
            self.button_frame_bottom,
            text="Parámetros de contorno",
            padx=10,
            pady=0,
            labelanchor="nw",
            font=("Arial", 10),
            width=630,
            height=170
        )
        Frame_Parametros_Contorno.pack_propagate(False) # Deshabilitar la redimensión automática
        Frame_Parametros_Contorno.pack(side=tk.TOP, anchor="w", padx=5, pady=0)
        ###################################################################################
        # Fila 1: Deslizadores
        ###################################################################################
        fila_4_frame = tk.Frame(Frame_Parametros_Contorno)
        fila_4_frame.pack(side=tk.TOP, fill="x", pady=5, anchor="nw")
        slider_height = 15
        slider_Longitud = 55
        frame_param1 = tk.Frame(fila_4_frame)
        frame_param1.pack(side=tk.LEFT, padx=14)
        tk.Label(frame_param1, text="Intensidad\nBordes").pack(side=tk.TOP, anchor="center")
        self.param1_value_label = tk.Label(frame_param1, text="50", font=("Arial", 9))
        self.param1_value_label.pack(side=tk.TOP)
        slider_band_param1 = tk.Frame(frame_param1, height=slider_height)
        slider_band_param1.pack(side=tk.TOP)
        btn_param1_minus = tk.Canvas(slider_band_param1, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param1_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_param1_minus_btn = tk.Button(
            btn_param1_minus,
            text="\u25C0",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param1_slider, -1, self.update_param1)
        )
        btn_param1_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param1_slider, -0.5, self.update_param1))
        btn_param1_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param1_minus.create_window(8, slider_height // 2, window=btn_param1_minus_btn, anchor="center")
        self.param1_slider = tk.Scale(
            slider_band_param1,
            from_=1, to=200,
            resolution=0.5,            
            orient=tk.HORIZONTAL,
            command=self.update_param1,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.param1_slider.set(50)
        self.param1_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.param1_slider, self.update_param1)
        btn_param1_plus = tk.Canvas(slider_band_param1, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param1_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_param1_plus_btn = tk.Button(
            btn_param1_plus,
            text="\u25B6",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param1_slider, +1, self.update_param1)
        )
        btn_param1_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param1_slider, +0.5, self.update_param1))
        btn_param1_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param1_plus.create_window(8, slider_height // 2, window=btn_param1_plus_btn, anchor="center")
        frame_param2 = tk.Frame(fila_4_frame)
        frame_param2.pack(side=tk.LEFT, padx=16)
        tk.Label(frame_param2, text="Umbral\nGeométrico").pack(side=tk.TOP, anchor="center")
        self.param2_value_label = tk.Label(frame_param2, text="30", font=("Arial", 9))
        self.param2_value_label.pack(side=tk.TOP)
        slider_band_param2 = tk.Frame(frame_param2, height=slider_height)
        slider_band_param2.pack(side=tk.TOP)
        btn_param2_minus = tk.Canvas(slider_band_param2, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param2_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_param2_minus_btn = tk.Button(
            btn_param2_minus,
            text="\u25C0",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param2_slider, -1, self.update_param2)
        )
        btn_param2_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param2_slider, -0.5, self.update_param2))
        btn_param2_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param2_minus.create_window(8, slider_height // 2, window=btn_param2_minus_btn, anchor="center")
        self.param2_slider = tk.Scale(
            slider_band_param2,
            from_=1, to=200,
            resolution=0.5,
            orient=tk.HORIZONTAL,
            command=self.update_param2,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.param2_slider.set(30)
        self.param2_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.param2_slider, self.update_param2)
        btn_param2_plus = tk.Canvas(slider_band_param2, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param2_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_param2_plus_btn = tk.Button(
            btn_param2_plus,
            text="\u25B6",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param2_slider, +1, self.update_param2)
        )
        btn_param2_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param2_slider, +0.5, self.update_param2))
        btn_param2_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param2_plus.create_window(8, slider_height // 2, window=btn_param2_plus_btn, anchor="center")
        frame_min_dist = tk.Frame(fila_4_frame)
        frame_min_dist.pack(side=tk.LEFT, padx=5)
        tk.Label(frame_min_dist, text="Separación\nentre centros").pack(side=tk.TOP, anchor="center")
        self.min_dist_value_label = tk.Label(frame_min_dist, text="1", font=("Arial", 9))
        self.min_dist_value_label.pack(side=tk.TOP)
        slider_band_min_dist = tk.Frame(frame_min_dist, height=slider_height)
        slider_band_min_dist.pack(side=tk.TOP)
        btn_min_dist_minus = tk.Canvas(slider_band_min_dist, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_dist_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_min_dist_minus_btn = tk.Button(
            btn_min_dist_minus,
            text="\u25C0",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_dist_slider, -1, self.update_min_dist)
        )
        btn_min_dist_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_dist_slider, -1, self.update_min_dist))
        btn_min_dist_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_dist_minus.create_window(8, slider_height // 2, window=btn_min_dist_minus_btn, anchor="center")
        self.min_dist_slider = tk.Scale(
            slider_band_min_dist,
            from_=1, to=400,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.update_min_dist,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.min_dist_slider.set(1)
        self.min_dist_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.min_dist_slider, self.update_min_dist)
        btn_min_dist_plus = tk.Canvas(slider_band_min_dist, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_dist_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_min_dist_plus_btn = tk.Button(
            btn_min_dist_plus,
            text="\u25B6",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_dist_slider, +1, self.update_min_dist)
        )
        btn_min_dist_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_dist_slider, +1, self.update_min_dist))
        btn_min_dist_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_dist_plus.create_window(8, slider_height // 2, window=btn_min_dist_plus_btn, anchor="center")
        frame_min_radius = tk.Frame(fila_4_frame)
        frame_min_radius.pack(side=tk.LEFT, padx=4)
        tk.Label(frame_min_radius, text="Diámetro\nmínimo").pack(side=tk.TOP, anchor="center")
        self.min_radius_value_label = tk.Label(frame_min_radius, text="1", font=("Arial", 9))
        self.min_radius_value_label.pack(side=tk.TOP)
        slider_band_min_radius = tk.Frame(frame_min_radius, height=slider_height)
        slider_band_min_radius.pack(side=tk.TOP)
        btn_min_radius_minus = tk.Canvas(slider_band_min_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_radius_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_min_radius_minus_btn = tk.Button(
            btn_min_radius_minus,
            text="\u25C0",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_radius_slider, -1, self.update_min_radius)
        )
        btn_min_radius_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_radius_slider, -1, self.update_min_radius))
        btn_min_radius_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_radius_minus.create_window(8, slider_height // 2, window=btn_min_radius_minus_btn, anchor="center")
        self.min_radius_slider = tk.Scale(
            slider_band_min_radius,
            from_=1, to=400,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.update_min_radius,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.min_radius_slider.set(1)
        self.min_radius_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.min_radius_slider, self.update_min_radius)
        btn_min_radius_plus = tk.Canvas(slider_band_min_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_radius_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_min_radius_plus_btn = tk.Button(
            btn_min_radius_plus,
            text="\u25B6",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_radius_slider, +1, self.update_min_radius)
        )
        btn_min_radius_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_radius_slider, +1, self.update_min_radius))
        btn_min_radius_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_radius_plus.create_window(8, slider_height // 2, window=btn_min_radius_plus_btn, anchor="center")
        frame_max_radius = tk.Frame(fila_4_frame)
        frame_max_radius.pack(side=tk.LEFT, padx=22)
        tk.Label(frame_max_radius, text="Diámetro\nmáximo").pack(side=tk.TOP, anchor="center")
        self.max_radius_value_label = tk.Label(frame_max_radius, text="1", font=("Arial", 9))
        self.max_radius_value_label.pack(side=tk.TOP)
        slider_band_max_radius = tk.Frame(frame_max_radius, height=slider_height)
        slider_band_max_radius.pack(side=tk.TOP)
        btn_max_radius_minus = tk.Canvas(slider_band_max_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_max_radius_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_max_radius_minus_btn = tk.Button(
            btn_max_radius_minus,
            text="\u25C0",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.max_radius_slider, -1, self.update_max_radius)
        )
        btn_max_radius_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.max_radius_slider, -1, self.update_max_radius))
        btn_max_radius_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_max_radius_minus.create_window(8, slider_height // 2, window=btn_max_radius_minus_btn, anchor="center")
        self.max_radius_slider = tk.Scale(
            slider_band_max_radius,
            from_=1, to=400,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.update_max_radius,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.max_radius_slider.set(1)
        self.max_radius_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.max_radius_slider, self.update_max_radius)
        btn_max_radius_plus = tk.Canvas(slider_band_max_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_max_radius_plus.pack(side=tk.LEFT, padx=(0, 0))
        btn_max_radius_plus_btn = tk.Button(
            btn_max_radius_plus,
            text="\u25B6",
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.max_radius_slider, +1, self.update_max_radius)
        )
        btn_max_radius_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.max_radius_slider, +1, self.update_max_radius))
        btn_max_radius_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_max_radius_plus.create_window(8, slider_height // 2, window=btn_max_radius_plus_btn, anchor="center")
        fila_5_frame = tk.Frame(Frame_Parametros_Contorno)
        fila_5_frame.pack(side=tk.TOP, fill="x", pady=5, anchor="center")
        self.formas_contours = tk.Frame(fila_5_frame)
        self.formas_contours.pack(side=tk.LEFT, padx=5, pady=0)
        label_title = tk.Label(self.formas_contours, text="Selecciona un contorno:", font=("Arial", 10))
        label_title.pack(side=tk.TOP, anchor="nw", padx=0, pady=(5, 2))
        self.selected_shape = tk.StringVar(value="Círculos")
        rbtn_circles = tk.Radiobutton(
            self.formas_contours,
            text="Círculos",
            variable=self.selected_shape,
            value="Círculos",
            command=lambda: print("Seleccionado: Círculos"),
            font=("Arial", 10)
        )
        rbtn_circles.pack(side=tk.LEFT, anchor="nw", padx=0, pady=0)
        rbtn_others = tk.Radiobutton(
            self.formas_contours,
            text="Otros",
            variable=self.selected_shape,
            value="Otros",
            command=lambda: print("Seleccionado: Otros"),
            font=("Arial", 10)
        )
        rbtn_others.pack(side=tk.LEFT, anchor="w", padx=5, pady=0)
        btn_clear_contours = tk.Button(fila_5_frame, text="Limpiar\nimagen", font=("Arial", 9), command=self.clear_contours)
        btn_clear_contours.pack(side=tk.LEFT, padx=5, pady=5)
        apply_changes_button = tk.Button(fila_5_frame, text="Aplicar", command=lambda: self.apply_parameters(
            self.min_dist_slider.get(),
            self.param1_slider.get(),
            self.param2_slider.get(),
            self.min_radius_slider.get(),
            self.max_radius_slider.get()
        ))
        apply_changes_button.pack(side=tk.LEFT, padx=5, pady=5)
        reset_button = tk.Button(fila_5_frame, text="Reiniciar\nvalores", font=("Arial", 9), command=self.reset_sliders_and_image)
        reset_button.pack(side=tk.LEFT, padx=5, pady=5)
        btn_count_contours = tk.Button(fila_5_frame, text="Contar", command=self.count_contours)
        btn_count_contours.pack(side=tk.LEFT, padx=5, pady=5)
        btn_detectar_ref = tk.Button(fila_5_frame, text="Automático", command=self.buscar_candidatos_similares_automaticamente)
        btn_detectar_ref.pack(side=tk.LEFT, padx=5, pady=5)
        self.agregar_tooltip(btn_detectar_ref, "Ejecuta:\n --> Seleccionar\n --> Buscar\n --> Automático")
    #
    #####################################################################################################
    #####################################################################################################
    #                              Botones y miniaturas de la parte inferior                            #
    #####################################################################################################
    #
    # Función para configurar el frame inferior con miniaturas
    def setup_bottom_frame(self):    
        self.FrameMiniatura = tk.Frame(
            self.bottom_frame,
            bg=self.cget("bg"),
            width=1300, height=160
        )
        self.FrameMiniatura.grid(row=1, column=0, padx=5, pady=0, sticky="ew")
        self.FrameMiniatura.grid_propagate(False)
        self.thumbnail_canvas = tk.Canvas(
            self.FrameMiniatura,
            width=1300, 
            height=140, 
            bg=self.cget("bg"), 
            highlightthickness=0
        )
        self.thumbnail_canvas.grid(row=0, column=0, sticky="ew")
        self.thumbnail_scroll_frame = tk.Frame(self.thumbnail_canvas, bg=self.cget("bg"))
        self.thumbnail_canvas.create_window((0, 0), window=self.thumbnail_scroll_frame, anchor="nw")
        self.thumbnail_scroll_x = tk.Scrollbar(self.FrameMiniatura, orient="horizontal", command=self.thumbnail_canvas.xview, width=12)
        self.thumbnail_scroll_x.grid(row=1, column=0, sticky="ew")
        self.thumbnail_canvas.configure(xscrollcommand=self.thumbnail_scroll_x.set)
        self.thumbnail_scroll_frame.bind("<Configure>", lambda _: self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all")))
        self.thumbnail_canvas.bind("<Enter>", lambda e: self.bind_mousewheel_to_horizontal_scroll())
        self.thumbnail_canvas.bind("<Leave>", lambda e: self.unbind_all_mousewheel())
        self.grid_rowconfigure(1, weight=0)
        self.grid_columnconfigure(0, weight=1)

    def bind_mousewheel_to_horizontal_scroll(self):
        self.bind_all("<MouseWheel>", self.scroll_horizontal_windows)
        self.bind_all("<Button-4>", self.scroll_horizontal_linux)
        self.bind_all("<Button-5>", self.scroll_horizontal_linux)
    def unbind_all_mousewheel(self):
        self.unbind_all("<MouseWheel>")
        self.unbind_all("<Button-4>")
        self.unbind_all("<Button-5>")
    def scroll_horizontal_windows(self, event):
        self.thumbnail_canvas.xview_scroll(-1 * (event.delta // 120), "units")
    def scroll_horizontal_linux(self, event):
        direction = -1 if event.num == 4 else 1
        self.thumbnail_canvas.xview_scroll(direction, "units")
    #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    ########       Funciones de los botones lado izquierdo debajo de la imagen       #########
    ########                                                                         #########
    ##########################################################################################
    ##########################################################################################
    #
    # Función para cargar imágenes desde un directorio
    def load_images(self):
        self.geometry("400x300")
        self.image_directory = filedialog.askdirectory()
        if self.image_directory:
            self.display_images(self.image_directory)

    # Función para actualizar el canvas con la imagen actual
    def refresh_images(self):
        if self.image_directory:
            self.display_images(self.image_directory)

    # Función para guardar la imagen procesada que se está mostrando en el canvas
    def save_image(self):
        if not hasattr(self, 'processed_image') or self.processed_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen procesada para guardar.")
            return
        base_name = os.path.basename(self.current_image_path or "imagen_procesada")
        initial_file_name = f"{os.path.splitext(base_name)[0]}_procesada.png"
        file_path = filedialog.asksaveasfilename(
            defaultextension=".png",
            initialfile=initial_file_name,
            filetypes=[
                ("PNG", "*.png"),
                ("JPEG", "*.jpg *.jpeg"),
                ("Bitmap", "*.bmp"),
                ("TIFF", "*.tif *.tiff"),
                ("Todos los archivos", "*.*")
            ],
            initialdir=self.image_directory
        )
        if file_path:
            cv2.imwrite(file_path, cv2.cvtColor(self.processed_image, cv2.COLOR_RGB2BGR))
            messagebox.showinfo("Imagen guardada", 
                              f"La imagen procesada se guardó correctamente")
    #
    ##########################################################################################
    ##########################################################################################
    ###################       Funciones de los botones lado derecho       ####################
    ###################                                                   ####################
    ##########################################################################################
    ##########################################################################################
    #
    # Función para hacer zoom in (acercar)
    def zoom_in(self):
        if self.original_image is None:
            return
        self.save_state()
        self.scale_factor = min(self.scale_factor*1.1, self.max_scale)
        self.update_zoom_display()
        self.redraw_contours()
        self.redraw_mediciones()

    # Función para hacer zoom out (alejar)
    def zoom_out(self):
        if self.original_image is None:
            return
        self.save_state()
        self.scale_factor = max(self.scale_factor/1.1, self.min_scale)
        self.update_zoom_display()
        self.redraw_contours()
        self.redraw_mediciones()

    # Función para aplicar el zoom actual a la imagen
    def apply_zoom(self):
        if self.temp_image is None:
            return
        source_img = self.temp_image
        if isinstance(source_img, Image.Image):
            img_pil = source_img
        else:
            img_pil = Image.fromarray(cv2.cvtColor(source_img, cv2.COLOR_BGR2RGB))
        new_width = int(self.original_width*self.scale_factor)
        new_height = int(self.original_height*self.scale_factor)
        if new_width <= 0 or new_height <= 0:
            messagebox.showwarning("Zoom inválido", "La imagen es demasiado pequeña para mostrar.")
            return
        resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
        self.img_tk = ImageTk.PhotoImage(resized)
        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)
        self.canvas.delete("image")
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=self.img_tk, tags="image")
        self.canvas.image = self.img_tk
        self.canvas.config(scrollregion=(0, 0, new_width, new_height))
        self._update_canvas_drawings()

    # Función para actualizar la conversión de zoom
    def actualizar_conversion_zoom(self):
        pix_val = self.ValorPixel.get()
        dist_val = self.ValorDistancia.get()
        if pix_val > 0 and dist_val > 0 and self.scale_factor > 0:
            self.ValorConversion = dist_val/(pix_val*self.scale_factor)
            self.conversion_label.config(text=f"{self.ValorConversion:.2f}")
            nuevo_limite = 400*self.ValorConversion
            min_radius_val = self.min_radius_slider.get()
            max_radius_val = self.max_radius_slider.get()
            min_dist_val = self.min_dist_slider.get()
            self.min_radius_slider.config(to=nuevo_limite)
            self.max_radius_slider.config(to=nuevo_limite)
            self.min_dist_slider.config(to=nuevo_limite)
            self.update_min_radius(min_radius_val)
            self.update_max_radius(max_radius_val)
            self.update_min_dist(min_dist_val)
        else:
            print("Conversión no actualizada: ValorPixel, ValorDistancia o escala inválidos.")

    # Función para convertir coordenadas visibles a coordenadas originales
    def get_original_coordinates(self, x, y):
        x_canvas = self.canvas.canvasx(x) - self.x_offset
        y_canvas = self.canvas.canvasy(y) - self.y_offset
        orig_x = x_canvas/self.scale_factor
        orig_y = y_canvas/self.scale_factor
        return orig_x, orig_y

    # Función para calcular las coordenadas centralizadas de la imagen
    def update_zoom_display(self):
        if self.temp_image is None:
            return
        source_img = self.temp_image
        if isinstance(source_img, Image.Image):
            img_pil = source_img
        else:
            img_rgb = cv2.cvtColor(source_img, cv2.COLOR_BGR2RGB)
            img_pil = Image.fromarray(img_rgb)
        new_width = int(self.original_width*self.scale_factor)
        new_height = int(self.original_height*self.scale_factor)
        img_resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
        img_tk = ImageTk.PhotoImage(img_resized)
        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)
        self.canvas.delete("image")
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=img_tk, tags="image")
        self.canvas.image = img_tk
        self.canvas.config(scrollregion=(0, 0, new_width, new_height))
        self._update_canvas_drawings()

    # Función para calcular las coordenadas centralizadas de la imagen
    def update_image(self):
        if self.original_image is None:
            return
        new_width = int(self.original_width*self.scale_factor)
        new_height = int(self.original_height*self.scale_factor)
        resized_image = self.original_image.resize((new_width, new_height), Image.Resampling.LANCZOS)
        self.image = ImageTk.PhotoImage(resized_image)
        x, y = self.calculate_centered_coordinates(new_width, new_height)
        self.canvas.delete("all")
        self.canvas.create_image(x, y, image=self.image, anchor="nw", tag="image")
        self.canvas.config(scrollregion=self.canvas.bbox("all"))
        self.canvas.image = self.image

    # Función que ajusta las coordenadas de un objeto en el canvas según el zoom y el desplazamiento
    def _rescale_canvas_item(self, item_id):
        original_coords = self.canvas.coords(item_id)
        scaled_coords = [
            (coord - self.x_offset)*self.scale_factor + self.x_offset if idx % 2 == 0 else
            (coord - self.y_offset)*self.scale_factor + self.y_offset
            for idx, coord in enumerate(original_coords)
        ]
        self.canvas.coords(item_id, *scaled_coords)

    # Función para calcular las coordenadas centralizadas de la imagen
    def _get_image_offsets(self):
        img_width = int(self.original_width*self.scale_factor)
        img_height = int(self.original_height*self.scale_factor)
        return self.calculate_centered_coordinates(img_width, img_height)

    # Función para restablecer la imagen original
    def _update_canvas_drawings(self):
        if self.line_id:
            self._rescale_canvas_item(self.line_id)
        if self.rect_id:
            self._rescale_canvas_item(self.rect_id)
        if hasattr(self, 'contour_canvas_ids'):
            for obj_id in self.contour_canvas_ids:
                self._rescale_canvas_item(obj_id)

    # Función para guardar el estado actual de la imagen y los parámetros
    def save_state(self):
        if self.temp_image is not None:
            tabla_datos = []
            for item in self.results_table.get_children():
                valores = self.results_table.item(item)["values"]
                tabla_datos.append(valores)
            state = {
                'image': self.temp_image.copy(),
                'scale_factor': self.scale_factor,
                'medicion_lineas': self.medicion_lineas.copy(),
                'medicion_rectangulos': self.medicion_rectangulos.copy(),
                'tabla_resultados': tabla_datos,
                'segmentacion_actual': self.segment_menu_button.cget("text"),                
                'sliders': {
                    'equalize_hist': self.slider_equalize_hist.get(),
                    'contrast': self.slider_contrast.get(),
                    'min_radius': self.min_radius_slider.get(),
                    'max_radius': self.max_radius_slider.get(),
                    'min_dist': self.min_dist_slider.get()
                },
                'patron_intensidad_referencia': self.patron_intensidad_referencia.copy() if hasattr(self, 'patron_intensidad_referencia') and self.patron_intensidad_referencia is not None else None,
                'radio_referencia_manual': getattr(self, 'radio_referencia_manual', None)
            }
            self.undo_stack.append(state)
            if getattr(self, 'just_undone', False):
                self.redo_stack.clear()
                self.just_undone = False

    # Función para deshacer el último cambio realizado
    def undo_change(self):
        if not self.undo_stack:
            messagebox.showinfo("Deshacer", "No hay cambios para deshacer.")
            return
        self.just_undone = True
        current_state = {
            'image': self.temp_image.copy(),
            'scale_factor': self.scale_factor,
            'medicion_lineas': self.medicion_lineas.copy(),
            'medicion_rectangulos': self.medicion_rectangulos.copy(),
            'segmentacion_actual': self.segment_menu_button.cget("text"),            
            'sliders': {
                'equalize_hist': self.slider_equalize_hist.get(),
                'contrast': self.slider_contrast.get(),
                'min_radius': self.min_radius_slider.get(),
                'max_radius': self.max_radius_slider.get(),
                'min_dist': self.min_dist_slider.get()
            }
        }
        self.redo_stack.append(current_state)
        prev_state = self.undo_stack.pop()
        self.temp_image = prev_state['image']
        self.scale_factor = prev_state.get('scale_factor', 1.0)
        self.medicion_lineas = prev_state.get('medicion_lineas', [])
        self.medicion_rectangulos = prev_state.get('medicion_rectangulos', [])
        sliders = prev_state['sliders']
        self.slider_equalize_hist.set(sliders['equalize_hist'])
        self.slider_contrast.set(sliders['contrast'])
        self.min_radius_slider.set(sliders['min_radius'])
        self.max_radius_slider.set(sliders['max_radius'])
        self.min_dist_slider.set(sliders['min_dist'])
        self.update_zoom_display()
        self.sync_sliders(sliders)
        self.redraw_contours()
        self.redraw_mediciones()
        segmentacion = prev_state.get('segmentacion_actual', "Segmentar color \u25BC")
        self.segment_menu_button.config(text=segmentacion)
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        if "Color" in segmentacion:
            self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
            self.color1_button.pack(side=tk.LEFT, padx=2)
            self.color2_button.pack(side=tk.LEFT, padx=2)
            self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color_hint_label.pack(side=tk.TOP)
        elif "K-means" in segmentacion:
            self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
            self.k_hint_label.pack(side=tk.TOP)
            self.k_entry.config(state="normal")

    # Función para rehacer el último cambio deshecho
    def redo_change(self):
        if not self.redo_stack:
            messagebox.showinfo("Rehacer", "No hay cambios para rehacer.")
            return
        current_state = {
            'image': self.temp_image.copy(),
            'scale_factor': self.scale_factor,
            'medicion_lineas': self.medicion_lineas.copy(),
            'medicion_rectangulos': self.medicion_rectangulos.copy(),
            'segmentacion_actual': self.segment_menu_button.cget("text"),
            'sliders': {
                'equalize_hist': self.slider_equalize_hist.get(),
                'contrast': self.slider_contrast.get(),
                'min_radius': self.min_radius_slider.get(),
                'max_radius': self.max_radius_slider.get(),
                'min_dist': self.min_dist_slider.get()
            }
        }
        self.undo_stack.append(current_state)
        next_state = self.redo_stack.pop()
        self.temp_image = next_state['image']
        self.scale_factor = next_state.get('scale_factor', 1.0)
        self.medicion_lineas = next_state.get('medicion_lineas', [])
        self.medicion_rectangulos = next_state.get('medicion_rectangulos', [])
        sliders = next_state['sliders']
        self.slider_equalize_hist.set(sliders['equalize_hist'])
        self.slider_contrast.set(sliders['contrast'])
        self.min_radius_slider.set(sliders['min_radius'])
        self.max_radius_slider.set(sliders['max_radius'])
        self.min_dist_slider.set(sliders['min_dist'])
        self.update_zoom_display()
        self.sync_sliders(sliders)
        self.redraw_contours()
        self.redraw_mediciones()
        segmentacion = next_state.get('segmentacion_actual', "Segmentar color \u25BC")
        self.segment_menu_button.config(text=segmentacion)
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        if "Color" in segmentacion:
            self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
            self.color1_button.pack(side=tk.LEFT, padx=2)
            self.color2_button.pack(side=tk.LEFT, padx=2)
            self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color_hint_label.pack(side=tk.TOP)
        elif "K-means" in segmentacion:
            self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
            self.k_hint_label.pack(side=tk.TOP)
            self.k_entry.config(state="normal")

    # Función para tomar una foto desde la pestaña activa
    def take_photo(self):
        start_time = time.time()
        active_tab = self.notebook.index(self.notebook.select())
        if active_tab == 0:
            image_data = self.capture_widget(self.canvas_tab)
        elif active_tab == 1:
            image_data = self.capture_widget(self.canvas_tab_temp)
        elif active_tab == 2:
            image_data = self.capture_widget(self.canvas_tab_results)
        elif active_tab == 3:
            image_data = self.capture_widget(self.camera_tab)
        else:
            return
        if image_data is None:
            messagebox.showerror("Error", "No se pudo capturar la imagen.")
            return
        self.current_image = image_data
        file_path = tk.filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("Archivos PNG", "*.png"), ("Todos los archivos", "*.*")],
            title="Guardar imagen"
        )
        if not file_path:
            return
        cv2.imwrite(file_path, self.current_image)
        self.load_image(file_path)

    # Función para capturar el contenido del canvas y convertirlo en una imagen
    def capture_widget(self, widget):
        if isinstance(widget, tk.Canvas):
            canvas = widget
        else:
            canvas = widget.winfo_children()[0] if widget.winfo_children() else None
        if canvas is None or not isinstance(canvas, tk.Canvas):
            messagebox.showerror("Error", "No se encontró un Canvas dentro del widget.")
            return None
        ps = canvas.postscript(colormode='color')
        img = Image.open(io.BytesIO(ps.encode('utf-8')))
        img = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR)
        return img

    # Función para mostrar un mensaje de ayuda al usuario
    def ayuda_usuario(self):
        ventana_ayuda = tk.Toplevel(self)
        ventana_ayuda.title("Ayuda del sistema")
        ventana_ayuda.geometry("750x600")
        ventana_ayuda.resizable(True, True)
        tk.Label(ventana_ayuda, text="Descripción de la interfaz del sistema UAdeO-SICS", font=("Arial", 14, "bold")).pack(pady=(10, 0))
        frame_texto = tk.Frame(ventana_ayuda)
        frame_texto.pack(fill="both", expand=True, padx=10, pady=10)
        scroll = tk.Scrollbar(frame_texto)
        scroll.pack(side="right", fill="y")
        texto = tk.Text(
            frame_texto,
            wrap="word",
            yscrollcommand=scroll.set,
            font=("Courier New", 12),
            bg="#f9f9f9",
            padx=12,
            pady=10
        )
        texto.pack(side="left", fill="both", expand=True)
        scroll.config(command=texto.yview)
        texto.tag_configure("espaciado", spacing1=4, spacing2=4, spacing3=6)
        contenido = (
        "Guía de botones y funciones principales\n\n"
        "Pestañas de visualización\n"
        "• Imagen temporal: Muestra la imagen actual con los últimos ajustes o procesamiento aplicado.\n"
        "• Imagen original: Visualiza la imagen tal como fue cargada, sin modificaciones.\n"
        "• Cámara: Muestra el video en tiempo real desde la cámara seleccionada y permite capturar imágenes para analizarlas.\n"
        "• Resultados: Presenta una tabla con las mediciones registradas, una gráfica de distribución y estadísticas como promedio y la desviación estándar.\n\n"

        "Parámetros de referencia\n"
        "• Medir referencia: Traza una línea sobre la imagen para establecer la escala entre píxeles y unidades físicas. Se activa cuando el botón está en verde.\n"
        "• Pixeles: Muestra o permite ingresar manualmente la distancia en píxeles de la línea trazada. Se registra cuando el botón está en verde.\n"
        "• Referencia: Permite introducir manualmente la distancia real correspondiente (nm, µm, mm, etc.). Se registra cuando el botón está en verde.\n"
        "• Aplicar: Calcula la equivalencia unidad/píxel. El valor se registra cuando el botón está en rojo.\n"
        "• Longitud: Mide distancias dentro de la imagen utilizando la escala establecida. Se activa cuando el botón está en verde.\n"
        "• Agregar a la tabla: Guarda automáticamente en la tabla las mediciones obtenidas con el trazo activado por el botón <Longitud>. Permanece activo mientras el botón está en azul.\n"
        "• Reiniciar valores: Restablece los valores actuales de longitud y escala a su estado inicial.\n\n"

        "Procesamiento de imagen\n"
        "• Reiniciar imagen: Restaura la imagen procesada a su estado original.\n"
        "• Intensidad: Ajusta la intensidad de la imagen para mejorar contraste interno.\n"
        "• Contraste: Modifica el contraste general de la imagen para resaltar detalles.\n"
        "• Seleccionar: Permite marcar manualmente un patrón de referencia sobre la imagen (por ejemplo, el contorno de una nanopartícula). El usuario traza un círculo que se utilizará como plantilla de búsqueda.\n"
        "• Seleccionar --> Buscar: Tras marcar un patrón con 'Seleccionar', este botón activa una búsqueda por coincidencia de intensidad utilizando la plantilla seleccionada. Se marcan en la imagen todas las regiones similares al patrón.\n"
        "• Segmentar color: Activa la herramienta para seleccionar dos colores utilizados en la segmentación.\n"
        "• Color 1 y Color 2: Confirma y bloquea los colores seleccionados desde la imagen.\n"
        "• Invertir colores: Invierte los colores de la imagen (efecto negativo).\n"
        "• Imagen en grises: Convierte la imagen a escala de grises.\n"
        "• Imagen binaria: Aplica un umbral automático (Otsu) para convertir la imagen en blanco y negro.\n"
        "• Segmentar por color: Activa la herramienta para seleccionar dos colores que se usarán para separar regiones.\n"
        "• Segmentar color --> Color 1 y Color 2: Permiten confirmar y fijar los colores seleccionados desde la imagen.\n"
        "• Segmentar color --> Separar objetos: Útil cuando hay elementos juntos o superpuestos; separa automáticamente los objetos.\n"
        "• Segmentar color --> Colores similares: Agrupa regiones con colores parecidos sin tener que seleccionar manualmente.\n\n"

        "Parámetros de contorno\n"
        "• Bordes Intensidad: Ajusta la sensibilidad de detección de bordes.\n"
        "• Bordes Umbral: Define el umbral mínimo para considerar un borde como válido.\n"
        "• Separación-centros: Establece la distancia mínima entre los centros de los objetos detectados.\n"
        "• Diámetros: Define los valores mínimo y máximo del diámetro de los objetos circulares a detectar.\n"
        "• Selección de contorno: Permite elegir entre detectar Círculos u otras formas irregulares.\n"
        "• Limpiar imagen: Elimina todos los contornos dibujados en la imagen.\n"
        "• Aplicar cambios: Aplica los valores configurados en los deslizadores.\n"
        "• Reiniciar valores: Restaura los parámetros de contorno a sus valores por defecto.\n"
        "• Contar: Ejecuta el análisis para detectar y contabilizar objetos.\n"
        "• Automático: Realiza la búsqueda de contornos similares al patrón seleccionado manualmente mediante la secuencia 'Seleccionar --> Buscar --> Automático'. Si no se ha definido un patrón, utiliza directamente los valores establecidos en los deslizadores (diámetro mínimo/máximo, separación entre centros, intensidad de bordes) para detectar regiones circulares de forma automática.\n\n"

        "Botones de cámara\n"
        "• Cámara: Despliega un menú con opciones para activar o desactivar cámaras conectadas.\n"
        "• Cámara --> Buscar cámaras: Escanea y muestra las cámaras disponibles para su selección.\n"
        "• Tomar foto: Captura la imagen mostrada en la pestaña <Imagen temporal> o desde la cámara seleccionada. La imagen tomada puede guardarse y se visualizará en la pestaña <Imagen temporal>.\n\n"

        "Otros botones\n"
        "• Directorio: Abre la carpeta de trabajo que contiene las imágenes para procesar.\n"
        "• Actualizar: Actualiza las miniaturas de imágenes cargadas desde el directorio.\n"
        "• Guardar imagen: Guarda la imagen procesada.\n"
        "• Limpiar tabla: Elimina todos los registros de la tabla de resultados.\n"
        "• Exportar datos: Guarda los resultados numéricos en un archivo con extensión '.dat'.\n"
        "• Gráfica: Genera un histograma de las mediciones en la pestaña <Resultados> y muestra estadísticas descriptivas como promedio y la desviación estándar.\n"
        )
        texto.insert("1.0", contenido, "espaciado")
        texto.config(state="disabled")
        tk.Button(ventana_ayuda, text="Cerrar", command=ventana_ayuda.destroy).pack(pady=5)
    #
    ##########################################################################################
    #****************************************************************************************#
    ###################             Funciones de los botones            ######################
    ###################             Parámetros de referencia            ######################
    #****************************************************************************************#
    ##########################################################################################
    #
    # Función para mostrar la imagen en pantalla
    def toggle_measurement(self):
        if self.is_measuring_reference or self.is_measuring_rectangle:
            self.disable_measurement()
        else:
            self.enable_measurement()

    # Función para habilitar la medición
    def enable_measurement(self):
        self.is_measuring_reference = True
        self.canvas.bind("<ButtonPress-1>", self.start_line)
        self.canvas.bind("<B1-Motion>", self.draw_line)
        self.canvas.bind("<ButtonRelease-1>", self.finish_line)
        self.is_measuring_rectangle = False
        self.canvas.unbind("<ButtonPress-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")

    # Función para deshabilitar la medición
    def disable_measurement(self):
        self.is_measuring_reference = False
        self.is_measuring_rectangle = False
        self.canvas.unbind("<ButtonPress-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.reset_state()

    # Función para restablecer el estado de líneas y rectángulos
    def reset_state(self):
        self.line_id = None
        self.rect_id = None
        self.start_x = None
        self.start_y = None

    # Función para ajustar las coordenadas de un objeto en el canvas según el zoom
    def adjust_coordinates(self, x_canvas, y_canvas):
        adjusted_x = (x_canvas - self.x_offset)/self.scale_factor
        adjusted_y = (y_canvas - self.y_offset)/self.scale_factor
        return adjusted_x, adjusted_y

    # Función para iniciar la medición del trazo de una línea en el canvas
    def start_line(self, event):
        self.save_state()
        self.start_x, self.start_y = self.get_original_coordinates(event.x, event.y)
        self.line_id = self.canvas.create_line(
            event.x, event.y, event.x, event.y, fill="red", width=2, tags="medicion"
        )

    # Función para actualizar el trazo de la línea mientras se arrastra el mouse
    def draw_line(self, event):
        if self.start_x is None or self.start_y is None:
            return
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        self.canvas.coords(
            self.line_id,
            self.start_x*self.scale_factor + self.x_offset,
            self.start_y*self.scale_factor + self.y_offset,
            end_x*self.scale_factor + self.x_offset,
            end_y*self.scale_factor + self.y_offset
        )

    # Función para redibujar las líneas de medición en el canvas
    def redraw_mediciones(self):
        self.canvas.delete("medicion")
        for x0, y0, x1, y1 in self.medicion_lineas:
            self.canvas.create_line(
                x0*self.scale_factor + self.x_offset,
                y0*self.scale_factor + self.y_offset,
                x1*self.scale_factor + self.x_offset,
                y1*self.scale_factor + self.y_offset,
                fill="red", width=2, tags="medicion"
            )
        for x0, y0, x1, y1 in self.medicion_rectangulos:
            self.canvas.create_rectangle(
                x0*self.scale_factor + self.x_offset,
                y0*self.scale_factor + self.y_offset,
                x1*self.scale_factor + self.x_offset,
                y1*self.scale_factor + self.y_offset,
                outline="red", width=2, tags="medicion"
        )

    # Función para finalizar el trazo de la línea y calcula la distancia
    def finish_line(self, event):
        if self.start_x is None or self.start_y is None:
            return 
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        distance = sqrt((end_x - self.start_x) ** 2 + (end_y - self.start_y) ** 2)
        self.MedicionPixeles = distance
        self.pixels_entry.delete(0, tk.END)
        self.pixels_entry.insert(0, f"{distance:.2f}")
        self.realizar_calculo()
        self.save_state()
        if self.agregar_a_tabla:
            num = len(self.results_table.get_children()) + 1
            self.results_table.insert("", "end", values=(num, f"{self.ValorLongitud.get():.2f}"))
        self.medicion_lineas.append((self.start_x, self.start_y, end_x, end_y))
        self.line_id = None
        self.start_x, self.start_y = None, None

    # Función para habilitar el modo de dibujo del rectángulo
    def enable_rectangle_mode(self):
        self.canvas.bind("<ButtonPress-1>", self.start_rectangle)
        self.canvas.bind("<B1-Motion>", self.update_rectangle)
        self.canvas.bind("<ButtonRelease-1>", self.finish_rectangle)   

    # Función para dibujar el rectángulo
    def start_rectangle(self, event):
        self.save_state()
        self.start_x, self.start_y = self.adjust_coordinates(event.x, event.y)
        self.rect_id = self.canvas.create_rectangle(
            event.x, event.y, event.x, event.y, outline="red", width=2, tags="medicion"
        )

    # Función para actualizar las dimensiones del rectángulo mientras se dibuja
    def update_rectangle(self, event):
        end_x, end_y = self.adjust_coordinates(event.x, event.y)
        self.canvas.coords(
            self.rect_id,
            self.start_x*self.scale_factor + self.x_offset,
            self.start_y*self.scale_factor + self.y_offset,
            end_x*self.scale_factor + self.x_offset,
            end_y*self.scale_factor + self.y_offset
        )

    # Función para finalizar el dibujo del rectángulo y actualizar las variables
    def finish_rectangle(self, event):
        end_x, end_y = self.adjust_coordinates(event.x, event.y)
        largo = abs(end_x - self.start_x)
        ancho = abs(end_y - self.start_y)
        largo_real = largo/self.scale_factor
        ancho_real = ancho/self.scale_factor
        self.ValorLargo.set(largo_real)
        self.ValorAncho.set(ancho_real)
        self.realizar_calculo()
        self.rect_id = None        
        self.medicion_rectangulos.append((self.start_x, self.start_y, end_x, end_y))

    # Función para dibujar un rectángulo en el canvas  teniendo en cuenta la escala y los desplazamientos
    def draw_rectangle(self, event):
        if self.start_x is None or self.start_y is None:
            self.start_x, self.start_y = event.x, event.y
        scaled_start_x = (self.start_x - self.canvas_x_offset)/self.image_scale
        scaled_start_y = (self.start_y - self.canvas_y_offset)/self.image_scale
        scaled_end_x = (event.x - self.canvas_x_offset)/self.image_scale
        scaled_end_y = (event.y - self.canvas_y_offset)/self.image_scale
    #
    ##########################################################################################
    #*********       Funciones de los botones de Parámetros de referencia        ************#
    #***********************              2da Fila                    ***********************#
    #***********    Cálculo de distancias y validación de captura de datos      *************#
    ##########################################################################################
    #
    # Función para validar si el valor ingresado es numérico
    def validar_numero(self, value):
        if value == "" or value.replace(".", "", 1).isdigit():
            return True
        return False

    # Función para validar y actualizar las variables: Sincroniza las variables con los campos de entrada
    def validar_y_actualizar(self, *args):
        try:
            self.ValorPixel.set(float(self.pixels_entry.get()))
            self.ValorDistancia.set(float(self.distance_entry.get()))
            if hasattr(self, 'length_entry') and self.length_entry is not None:
                self.ValorLongitud.set(float(self.length_entry.get()))
        except ValueError:
            self.pixels_entry.delete(0, tk.END)
            self.pixels_entry.insert(0, "0.0")
            pass

    # Función para validar y calcular la conversión de píxeles a distancia mediante la tecla Enter
    def validar_y_calcular(self, event=None):
        self.validar_y_actualizar()
        self.realizar_calculo()
        self.toggle_estado_boton("pixels")

    # Función para activar o desactivar los botones de píxeles y distancia
    def toggle_estado_boton(self, button_type):
        if button_type == "pixels":
            self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
            self.button_states["pixels"] = True
            self.pixels_entry.config(state=tk.DISABLED)
            self.distance_button.config(state=tk.NORMAL)
            self.distance_entry.config(state=tk.NORMAL)
        elif button_type == "distance":
            self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")
            self.button_states["distance"] = True
            self.distance_entry.config(state=tk.DISABLED)
            self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
            self.button_states["pixels"] = True
            self.pixels_entry.config(state=tk.DISABLED)

    # Realiza el cálculo de conversión usando los valores de píxeles y distancia
    def realizar_calculo(self):
        try:
            valor_pixel = self.ValorPixel.get()
            valor_distancia = self.ValorDistancia.get()
            if valor_pixel <= 0 or valor_distancia <= 0:
                return
            conversion = valor_distancia/valor_pixel
            self.ValorConversion = conversion
            self.conversion_label.config(text=f"{conversion:.2f}")
            if self.MedicionPixeles > 0:
                nueva_longitud = self.MedicionPixeles*conversion
                self.lengthLine_entry.delete(0, tk.END)
                self.lengthLine_entry.insert(0, f"{nueva_longitud:.2f}")
                self.ValorLongitud.set(nueva_longitud)
            nuevo_limite = 400*conversion
            self.min_radius_slider.config(state=tk.NORMAL, to=nuevo_limite)
            self.max_radius_slider.config(state=tk.NORMAL, to=nuevo_limite)
            self.min_dist_slider.config(state=tk.NORMAL, to=nuevo_limite)
            self.update_min_radius(self.min_radius_slider.get())
            self.update_max_radius(self.max_radius_slider.get())
            self.update_min_dist(self.min_dist_slider.get())
            largo = self.ValorLargo.get()
            ancho = self.ValorAncho.get()
            if largo > 0 and ancho > 0:
                nuevo_largo = largo*conversion
                nuevo_ancho = ancho*conversion
                self.ladoL_entry.delete(0, tk.END)
                self.ladoL_entry.insert(0, f"{nuevo_largo:.2f}")
                self.ladoA_entry.delete(0, tk.END)
                self.ladoA_entry.insert(0, f"{nuevo_ancho:.2f}")
        except Exception as e:
            messagebox.showerror("Error", f"Entrada inválida: {e}")
            default_slider_values = {'equalize_hist': 0, 'contrast': 0}
            self.sync_sliders(default_slider_values)

    # Función para resetear las mediciones y campos de entrada
    def reset_measurement(self):
        self.start_x, self.start_y = None, None
        self.rect_id = None
        self.line_id = None
        self.MedicionPixeles = 0.0
        self.ValorLargo.set(0.0)
        self.ValorAncho.set(0.0)
        self.ValorConversion = 1.0
        self.ValorPixel.set(0.0)
        self.ValorDistancia.set(0.0)
        self.ValorLongitud.set(0.0)
        self.pixels_entry.delete(0, tk.END)
        self.pixels_entry.insert(0, "0.0")
        self.distance_entry.delete(0, tk.END)
        self.distance_entry.insert(0, "0.0")
        self.lengthLine_entry.delete(0, tk.END)
        self.lengthLine_entry.insert(0, "0.0")
        self.distance_units_var.set("px")
        self.update_labels(self.distance_units_var.get())        
        radio_text = f"({self.distance_units_var.get()})"
        nuevo_limite_maximo = 400
        self.max_radius_slider.config(to=nuevo_limite_maximo)
        nuevo_limite_minimo = 400
        self.min_radius_slider.config(to=nuevo_limite_minimo)
        nuevo_limite_dist = 400
        self.min_dist_slider.config(to=nuevo_limite_dist)

    # Función para actualizar las etiquetas de unidades de medida
    def update_labels(self, new_unit):
        self.lengthLine_unit_label.config(text=new_unit)
        self.unidadesConversion_label.config(text=f"{new_unit}/px")
        self.conversion_label.config(text=f"1.0")
        self.refresh_distance_labels()
    #
    ##########################################################################################
    #****************************************************************************************#
    ###################             Funciones de los botones            ######################
    ###################            procesamiento de imágenes            ######################
    #****************************************************************************************#
    ##########################################################################################
    #
    # Función para procesar la imagen y actualizarla en el canvas
    def process_and_update_image(self, process_function, *args, **kwargs):
        if self.temp_image is None:
            messagebox.showinfo("Procesamiento de imagen", "No hay imagen para procesar.")
            return
        self.save_state()
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        self.canvas.delete("medicion")
        self.medicion_lineas.clear()
        self.medicion_rectangulos.clear()
        self.line_id = None
        self.rect_id = None
        for cid in getattr(self, "evaluation_canvas_ids", []):
            self.canvas.delete(cid)
        self.evaluation_canvas_ids.clear()
        self.manual_annotations.clear()
        self.patron_intensidad_referencia = None
        self.radio_referencia_manual = None
        img = self.temp_image
        if isinstance(img, Image.Image):
            img = np.array(img)
        if img.ndim == 3 and img.shape[-1] == 4:
            img = cv2.cvtColor(img, cv2.COLOR_RGBA2RGB)
        processed_img = process_function(img, *args, **kwargs)
        self.temp_image = Image.fromarray(processed_img)
        self.display_cv_image(processed_img)

    # Función para restablecer la imagen original y los deslizadores
    def reset_image(self):
        if self.original_image is None:
            return
        self.save_state()
        self.temp_image = self.original_image.copy()
        self.scale_factor = 1.0
        self.update_zoom_display()
        default_slider_values = {'equalize_hist': 0, 'contrast': 0}
        self.sync_sliders(default_slider_values)
        self.lower_bound = None
        self.upper_bound = None
        self.update_color_display("N/A", "N/A", "N/A")
        self.is_selecting_color = True
        self.contour_original_coords.clear()
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.canvas.delete("medicion")
        self.medicion_lineas.clear()
        self.medicion_rectangulos.clear()
        self.line_id = None
        self.rect_id = None
        self.canvas.update_idletasks()
        self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        self.actualizar_metodo_segmentacion("Segmentar color")
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        self.patron_intensidad_referencia = None
        self.radio_referencia_manual = None
        self.btn_buscar.config(state=tk.DISABLED)

    # Función para sincronizar los deslizadores con los valores especificados
    def sync_sliders(self, values):
        self.slider_equalize_hist.set(values.get('equalize_hist', 0))
        self.slider_contrast.set(values.get('contrast', 0))

    # Función para equalizar el histograma de la imagen
    def update_equalize_hist(self, val):
        self.save_state()
        value = int(float(val))
        self.equalize_value_label.config(text=str(value))
        alpha = value/100.0
        def equalize_hist(image, alpha):
            original_image = image.copy()
            if len(original_image.shape) == 2:
                equalized = cv2.equalizeHist(original_image)
                return cv2.addWeighted(original_image, 1 - alpha, equalized, alpha, 0)
            else:
                yuv = cv2.cvtColor(original_image, cv2.COLOR_BGR2YUV)
                yuv[:, :, 0] = cv2.equalizeHist(yuv[:, :, 0])
                equalized = cv2.cvtColor(yuv, cv2.COLOR_YUV2BGR)
                return cv2.addWeighted(original_image, 1 - alpha, equalized, alpha, 0)
        self.process_and_update_image(equalize_hist, alpha)

    # Función para ajustar el contraste de la imagen
    def update_contrast(self, val):
        self.save_state()
        value = int(float(val))
        self.contrast_value_label.config(text=str(value))
        alpha = 1 + (value/100.0)
        beta = 0
        def adjust_contrast(image, alpha, beta):
            return cv2.convertScaleAbs(image, alpha=alpha, beta=beta)
        # Procesar la imagen con el ajuste de contraste
        self.process_and_update_image(adjust_contrast, alpha, beta)

    # Función para ajustar el radio mínimo de los círculos detectados
    def adjust_slider(self, slider, step, callback):
        current = slider.get()
        new_value = current + step
        new_value = max(slider.cget("from"), min(slider.cget("to"), new_value))
        slider.set(new_value)
        callback(new_value)
    #
    #*********************************************************************#
    #*********  Funciones para la segmentación de la imagen       ********#
    #*********************************************************************#
    #
    def actualizar_metodo_segmentacion(self, metodo_nombre):
        self.segment_menu_button.config(text=f"{metodo_nombre} \u25BC")
    def iniciar_color_segmentacion(self):
        self.ocultar_campo_k()
        self.actualizar_metodo_segmentacion("Segmentar x color")
        self.start_segmentation()
    def iniciar_otsu_segmentacion(self):
        self.save_state()
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        self.actualizar_metodo_segmentacion("Blanco y negro")
        self.apply_otsu_threshold()
    def iniciar_watershed_segmentacion(self):
        self.save_state()
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        self.actualizar_metodo_segmentacion("Separar objetos")
        self.segmentar_watershed()
    def preparar_kmeans(self):
        self.save_state()
        self.actualizar_metodo_segmentacion("Colores similares")
        self.ocultar_botones_color()
        self.ocultar_instruccion_color()
        self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
        self.k_hint_label.pack(side=tk.TOP)
        self.k_entry.config(state="normal")
        self.k_entry.focus_set()
    # Función para ocultar los botones de selección de color 1 y 2
    def ocultar_botones_color(self):
        self.color1_button.pack_forget()
        self.color2_button.pack_forget()
        self.color_buttons_frame.pack_forget()
    # Función para ocultar el campo de entrada K
    def ocultar_campo_k(self):
        self.k_entry.config(state="disabled")
        self.frame_k_entry.pack_forget()
        self.k_hint_label.pack_forget()
    # Función para ocultar la etiqueta de sugerencia de color
    def ocultar_instruccion_color(self):
        self.color_hint_label.pack_forget()
    # Asegura que la imagen esté en formato BGR (3 canales)
    def ensure_bgr_format(self, image):
        if len(image.shape) == 2 or image.shape[2] == 1:
            image = cv2.cvtColor(image, cv2.COLOR_GRAY2BGR)
        return image

    # Función par inciar el proceso de segmentación
    def start_segmentation(self):
        if self.temp_image is None:
            messagebox.showinfo("Segmentación", "No hay imagen cargada.")
            return
        self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
        self.color1_button.pack(side=tk.LEFT, padx=2)
        self.color2_button.pack(side=tk.LEFT, padx=2)
        self.color1_button.config(state=tk.NORMAL, relief=tk.RAISED)
        self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        self.color_hint_label.pack(side=tk.TOP)
        self.lower_bound = None
        self.upper_bound = None
        self.temp_color = None
        self.is_selecting_color = True
        self.current_selection = 'lower'
        self.canvas.bind("<Button-1>", self.handle_color_selection)

    # Función para manejar la selección de color en la imagen
    def handle_color_selection(self, event):
        if not self.is_selecting_color or self.temp_image is None:
            return
        color_rgb = self.get_selected_color(event.x, event.y)
        if color_rgb is None:
            return
        hsv_color = cv2.cvtColor(np.uint8([[color_rgb]]), cv2.COLOR_RGB2HSV)[0][0]
        self.temp_color = hsv_color
        self.update_color_display(color_rgb)

    # Función para confirmar la selección de color
    def confirm_color1(self):
        if self.temp_color is not None:
            self.lower_bound = np.clip(
                self.temp_color - np.array([10, 50, 50]),
                [0, 0, 0],
                [179, 255, 255]
            )
            self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color2_button.config(state=tk.NORMAL, relief=tk.RAISED)
            self.current_selection = 'upper'
            self.temp_color = None
            self.color_hint_label.config(text="Seleccione un color\ny presione el botón")

    # Función para confirmar la selección del Color 2 y aplicar la segmentación
    def confirm_color2(self):
        if self.temp_color is not None:
            self.upper_bound = np.clip(
                self.temp_color + np.array([10, 50, 50]),
                [0, 0, 0],
                [179, 255, 255]
            )
            self.save_state()
            self.finish_color_selection()

    # Función para finalizar el proceso de selección de colores
    def finish_color_selection(self):
        if self.lower_bound is None or self.upper_bound is None:
            return
        self.is_selecting_color = False
        self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        self.canvas.unbind("<Button-1>")
        self.apply_segmentation()
        self.lower_bound = None
        self.upper_bound = None
        self.temp_color = None
        self.color1_button.pack_forget()
        self.color2_button.pack_forget()
        self.color_buttons_frame.pack_forget()
        self.color_hint_label.pack_forget()

    # Obtiene el color RGB del píxel seleccionado en las coordenadas (x, y)
    def get_selected_color(self, x=None, y=None):
        if self.temp_image is None:
            return None
        img_np = self.temp_image
        if isinstance(img_np, Image.Image):
            img_np = np.array(img_np)
        if img_np.ndim == 3 and img_np.shape[-1] == 4:
            img_np = cv2.cvtColor(img_np, cv2.COLOR_RGBA2RGB)
        image_height, image_width = img_np.shape[:2]
        if x is None or y is None:
            x, y = image_width // 2, image_height // 2
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        scale_x = image_width/canvas_width
        scale_y = image_height/canvas_height
        img_x = int(x*scale_x)
        img_y = int(y*scale_y)
        if 0 <= img_x < image_width and 0 <= img_y < image_height:
            color_bgr = img_np[img_y, img_x]
            color_rgb = color_bgr[::-1]
            return color_rgb
        else:
            messagebox.showinfo("Información", "Coordenadas fuera de rango.")
            return None

    # Aplica la segmentación usando los límites de color seleccionados.
    def apply_segmentation(self):
        def process(image):
            image = self.ensure_bgr_format(image)
            hsv_image = cv2.cvtColor(image, cv2.COLOR_BGR2HSV)
            mask = cv2.inRange(hsv_image, self.lower_bound, self.upper_bound)
            segmented_image = cv2.bitwise_and(image, image, mask=mask)
            return segmented_image
        if self.temp_image is None or self.lower_bound is None or self.upper_bound is None:
            messagebox.showinfo("Información", "No hay parámetros para segmentar.")
            return
        self.process_and_update_image(process)

    # Actualiza la visualización del color seleccionado y el rango
    def update_color_display(self, color_rgb, lower_bound=None, upper_bound=None):
        if lower_bound is None or upper_bound is None:
            lower_bound, upper_bound = "N/A", "N/A"

    # Función para aplicar binarización a la imagen con Otzu
    def apply_otsu_threshold(self):
        self.save_state()
        def otsu_threshold(image):
            image = self.ensure_bgr_format(image)
            gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            _, thresh_image = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            return thresh_image
        self.process_and_update_image(otsu_threshold)

    # Función para segmentar la imagen usando el algoritmo Watershed  
    def segmentar_watershed(self):
        self.save_state()
        def watershed_segmentation(image):
            if image is None:
                return image
            img = self.ensure_bgr_format(image.copy())
            gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
            _, thresh = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            kernel = np.ones((3, 3), np.uint8)
            opening = cv2.morphologyEx(thresh, cv2.MORPH_OPEN, kernel, iterations=2)
            sure_bg = cv2.dilate(opening, kernel, iterations=3)
            dist_transform = cv2.distanceTransform(opening, cv2.DIST_L2, 5)
            _, sure_fg = cv2.threshold(dist_transform, 0.5 * dist_transform.max(), 255, 0)
            sure_fg = np.uint8(sure_fg)
            unknown = cv2.subtract(sure_bg, sure_fg)
            _, markers = cv2.connectedComponents(sure_fg)
            markers = markers + 1
            markers[unknown == 255] = 0
            markers = cv2.watershed(img, markers)
            img[markers == -1] = [0, 0, 255]
            return img
        self.process_and_update_image(watershed_segmentation)

    # Función para manejar la entrada del usuario al presionar Enter en el campo K
    def on_enter_k(self, event):
        if self.temp_image is None:
            messagebox.showwarning("Imagen no cargada", "Primero debe cargar una imagen.")
            return        
        try:
            k = int(self.k_entry.get())
            if k < 2:
                raise ValueError
            self.segmentar_kmeans_con_k(k)
            self.ocultar_campo_k()
        except ValueError:
            messagebox.showerror("Valor inválido", "Por favor, introduce un número entero mayor o igual a 2 para K.")

    # Función para segmentar la imagen usando K-means con el valor de K proporcionado
    def segmentar_kmeans_con_k(self, k):
        self.save_state()
        def kmeans_segmentation(image):
            if image is None:
                return image
            image = self.ensure_bgr_format(image)
            Z = image.reshape((-1, 3))
            Z = np.float32(Z)
            criterios = (cv2.TERM_CRITERIA_EPS + cv2.TERM_CRITERIA_MAX_ITER, 10, 1.0)
            _, etiquetas, centros = cv2.kmeans(Z, k, None, criterios, 10, cv2.KMEANS_RANDOM_CENTERS)
            centros = np.uint8(centros)
            segmentada = centros[etiquetas.flatten()].reshape(image.shape)
            return segmentada
        self.process_and_update_image(kmeans_segmentation)
    #
    ##########################################################################################
    #*********       Funciones de los botones de procesamiento de imágenes        ***********#
    #***********************              2da Fila                    ***********************#
    #*********************************                       ********************************#
    ##########################################################################################
    #
    # Función para invertir los colores de la imagen
    def invert_colors(self):
        self.save_state()
        def invert(image):
            return cv2.bitwise_not(image)
        self.process_and_update_image(invert)


    # Función para convertir la imagen a escala de grises
    def convert_to_grayscale(self):
        self.save_state()
        def to_grayscale(image):
            if len(image.shape) == 3:
                return cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            return image
        self.process_and_update_image(to_grayscale)
    #
    ##########################################################################################
    #*********       Funciones de los botones de parAmetros de contornos          ***********#
    #***********************              3ra Fila                    ***********************#
    #*********************************                       ********************************#
    ##########################################################################################
    #
    # Función para limpiar los contornos dibujados en la imagen
    def clear_contours(self):
        if self.temp_image is None:
            return
        self.save_state()
        if hasattr(self, 'contour_canvas_ids'):
            for obj_id in self.contour_canvas_ids:
                self.canvas.delete(obj_id)
            self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        self.canvas.delete("medicion")
        self.medicion_lineas.clear()
        self.medicion_rectangulos.clear()
        img_clean = self.temp_image.copy()
        new_width = int(img_clean.width*self.scale_factor)
        new_height = int(img_clean.height*self.scale_factor)
        img_resized = img_clean.resize((new_width, new_height), Image.Resampling.LANCZOS)
        self.img_tk = ImageTk.PhotoImage(img_resized)
        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=self.img_tk, tags="image")
        self.canvas.image = self.img_tk
        self.canvas.config(scrollregion=(0, 0, new_width, new_height))
        self.canvas.update_idletasks()

    # Funciones para actualizar los parámetros de la detección de círculos
    def update_param1(self, val):
        valor = int(float(val))
        self.param1 = valor
        porcentaje = valor / 2
        self.param1_value_label.config(text=f"{porcentaje:.1f}%")
    def update_param2(self, val):
        valor = int(float(val))
        self.param2 = valor
        porcentaje = valor / 2
        self.param2_value_label.config(text=f"{porcentaje:.1f}%")
    def refresh_distance_labels(self):
        unidad = self.distance_units_var.get()
        self.min_dist_value_label.config(text=f"{self.min_dist:.0f} {unidad}")
        self.min_radius_value_label.config(text=f"{self.min_radius:.0f} {unidad}")
        self.max_radius_value_label.config(text=f"{self.max_radius:.0f} {unidad}")
    def update_min_dist(self, val):
        valor = float(val)
        self.min_dist = valor
        unidad = self.distance_units_var.get()
        self.min_dist_value_label.config(text=f"{valor:.0f} {unidad}")
    def update_min_radius(self, val):
        valor = float(val)
        self.min_radius = valor
        unidad = self.distance_units_var.get()
        self.min_radius_value_label.config(text=f"{valor:.0f} {unidad}")
    def update_max_radius(self, val):
        valor = float(val)
        self.max_radius = valor
        unidad = self.distance_units_var.get()
        self.max_radius_value_label.config(text=f"{valor:.0f} {unidad}")

    # Función para restablecer los valores de los deslizadores y la imagen
    def reset_sliders_and_image(self):
        if self.ValorConversion <= 0:
            self.ValorConversion = 1.0
        default_min_dist = 20.0
        default_min_radius = 10.0
        default_max_radius = 50.0
        default_param1 = 50
        default_param2 = 30
        min_dist_px = int(default_min_dist/self.ValorConversion)
        min_radius_px = int(default_min_radius/self.ValorConversion)
        max_radius_px = int(default_max_radius/self.ValorConversion)
        max_slider_px = int(400/self.ValorConversion)
        self.min_dist_slider.config(from_=1, to=max_slider_px)
        self.min_radius_slider.config(from_=1, to=max_slider_px)
        self.max_radius_slider.config(from_=1, to=max_slider_px)
        self.min_dist_slider.set(min_dist_px)
        self.param1_slider.set(default_param1)
        self.param2_slider.set(default_param2)
        self.min_radius_slider.set(min_radius_px)
        self.max_radius_slider.set(max_radius_px)
        self.update_min_dist(min_dist_px)
        self.update_param1(default_param1)
        self.update_param2(default_param2)
        self.update_min_radius(min_radius_px)
        self.update_max_radius(max_radius_px)

    # Función para actualizar los parámetros con los valores ajustados por el usuario
    def update_parameters(self, min_dist, param1, param2, min_radius, max_radius):
        self.min_dist = min_dist
        self.param1 = param1
        self.param2 = param2
        self.min_radius = min_radius
        self.max_radius = max_radius

    # Función para aplicar los parámetros seleccionados ----#
    def on_apply_parameters_button_click(self):
        try:
            min_dist = float(self.min_dist_entry.get())
            param1 = float(self.param1_entry.get())
            param2 = float(self.param2_entry.get())
            min_radius = float(self.min_radius_entry.get())
            max_radius = float(self.max_radius_entry.get())
        except ValueError:
            messagebox.showwarning("Advertencia", "Ingrese valores válidos en todas las entradas.")
            return
        self.selected_shape.set("Círculos")
        self.apply_parameters(min_dist, param1, param2, min_radius, max_radius)

    # Función para aplicar parámetros seleccionados según la forma elegida
    def apply_parameters(self, min_dist, param1, param2, min_radius, max_radius):
        self.update_parameters(min_dist, param1, param2, min_radius, max_radius)
        if self.selected_shape.get() == "Círculos":
            self.update_image_for_circles(min_dist, param1, param2, min_radius, max_radius)
        elif self.selected_shape.get() == "Otros":
            self.update_image_for_amorphous(min_dist, param1, param2, min_radius, max_radius)
        else:
            messagebox.showwarning("Advertencia", "Selección inválida para los parámetros.")
            return

    # Función para contar los contornos circulares -----------------#
    def update_image_for_circles(self, min_dist, param1, param2, min_radius, max_radius):
        min_radius = min_radius/2
        max_radius = max_radius/2
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada para aplicar los parámetros.")
            return []
        if self.ValorConversion <= 0:
            messagebox.showwarning("Advertencia", "El factor de conversión es inválido.")
            return []
        img_np = np.array(self.temp_image)
        img_with_circles = img_np.copy()
        if len(img_with_circles.shape) == 2 or img_with_circles.shape[2] == 1:
            img_with_circles = cv2.cvtColor(img_with_circles, cv2.COLOR_GRAY2BGR)
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        img_gray = cv2.cvtColor(img_np, cv2.COLOR_RGB2GRAY) if img_np.ndim == 3 else img_np
        img_gray = cv2.bilateralFilter(img_gray, 9, 75, 75)
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
        img_gray = clahe.apply(img_gray)
        minRadius_pixels = int(min_radius/self.ValorConversion)
        maxRadius_pixels = int(max_radius/self.ValorConversion)
        minDist_pixels = min_dist/self.ValorConversion
        circles = cv2.HoughCircles(
            img_gray, cv2.HOUGH_GRADIENT, dp=1, minDist=minDist_pixels,
            param1=param1, param2=param2,
            minRadius=minRadius_pixels, maxRadius=maxRadius_pixels
        )
        num_circles = []
        if circles is not None:
            circles = np.uint16(np.around(circles))
            for i in circles[0, :]:
                radius_pixels = i[2]
                if minRadius_pixels <= radius_pixels <= maxRadius_pixels:
                    center = (i[0], i[1])
                    diameter_converted = radius_pixels
                    num_circles.append(diameter_converted)
                    circle_contour = [
                        (center[0] + radius_pixels*np.cos(t), center[1] + radius_pixels*np.sin(t))
                        for t in np.linspace(0, 2*np.pi, 20)
                    ]
                    original_circle_contour = [(x, y) for x, y in circle_contour]
                    self.contour_original_coords.append((original_circle_contour, "red"))
                    scaled = [(x*self.scale_factor + self.x_offset, y*self.scale_factor + self.y_offset)
                              for x, y in circle_contour]
                    flat = [coord for point in scaled for coord in point]
                    cid = self.canvas.create_line(flat, fill="red", width=2, smooth=True)
                    self.contour_canvas_ids.append(cid)
                    cv2.circle(img_with_circles, center, radius_pixels, (0, 0, 255), 2)
                    cv2.circle(img_with_circles, center, 2, (255, 0, 0), 3)
        self.processed_image = cv2.cvtColor(img_with_circles, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        return num_circles

    # Función para contar los contornos amorfos ---------------#
    def update_image_for_amorphous(self, min_dist, param1, param2, min_radius, max_radius):
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada para aplicar los parámetros.")
            return []
        img_with_contours = np.array(self.temp_image).copy()
        if len(img_with_contours.shape) == 2 or img_with_contours.shape[2] == 1:
            img_with_contours = cv2.cvtColor(img_with_contours, cv2.COLOR_GRAY2BGR)
        conversion = self.ValorConversion
        if conversion <= 0:
            messagebox.showwarning("Advertencia", "El factor de conversión es inválido.")
            return []
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        img_gray = cv2.cvtColor(img_with_contours, cv2.COLOR_RGB2GRAY) if img_with_contours.ndim == 3 else img_with_contours
        img_gray = cv2.bilateralFilter(img_gray, 9, 75, 75)
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
        img_gray = clahe.apply(img_gray)
        edges = cv2.Canny(img_gray, param1, param2)
        contours, _ = cv2.findContours(edges, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        filtered_contours = [
            cnt for cnt in contours if min_radius/conversion <= cv2.arcLength(cnt, True) <= max_radius/conversion
        ]
        for cnt in filtered_contours:
            points = [(int(p[0]), int(p[1])) for p in cnt.reshape(-1, 2)]
            self.contour_original_coords.append((points, "blue"))
            scaled = [(x*self.scale_factor + self.x_offset, y*self.scale_factor + self.y_offset) for x, y in points]
            flat = [coord for pt in scaled for coord in pt]
            cid = self.canvas.create_line(flat, fill="blue", width=2, smooth=True)
            self.contour_canvas_ids.append(cid)
        cv2.drawContours(img_with_contours, filtered_contours, -1, (255, 0, 0), 2)
        self.processed_image = cv2.cvtColor(img_with_contours, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        num_circles = [math.sqrt(cv2.contourArea(cnt)/math.pi) for cnt in filtered_contours]
        return num_circles

    # Función para contar y actualizar la tabla
    def count_contours(self):
        if self.original_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada para contar contornos.")
            return
        try:
            min_dist = self.min_dist
            param1 = self.param1
            param2 = self.param2
            min_radius = self.min_radius
            max_radius = self.max_radius
        except AttributeError as e:
            messagebox.showwarning("Advertencia", "Ajustar los parámetros antes de contar los contornos.")
            return
        if self.selected_shape.get() == "Círculos":
            num_circles = self.update_image_for_circles(min_dist, param1, param2, min_radius, max_radius)
        elif self.selected_shape.get() == "Otros":
            num_circles = self.update_image_for_amorphous(min_dist, param1, param2, min_radius, max_radius)
        else:
            messagebox.showwarning("Advertencia", "Por favor, seleccione una forma válida para contar los contornos.")
            return
        if num_circles:
            self.add_results_to_table(num_circles)
        else:
            messagebox.showwarning("Advertencia", "No se detectaron contornos en la imagen.")

    # Función para redibujar los contornos en el canvas
    def redraw_contours(self):
        for cid in self.contour_canvas_ids:
            self.canvas.delete(cid)
        self.contour_canvas_ids.clear()
        for contour, color in self.contour_original_coords:
            scaled = [(x*self.scale_factor + self.x_offset, y*self.scale_factor + self.y_offset)
                      for x, y in contour]
            flat = [coord for pt in scaled for coord in pt]
            cid = self.canvas.create_line(flat, fill=color, width=2, smooth=True)
            self.contour_canvas_ids.append(cid)

    # Función para agregar los resultados a la tabla
    def add_results_to_table(self, num_circles):
        medicion_num = len(self.results_table.get_children()) + 1
        for idx, radio in enumerate(num_circles, start=1):
            diametro = 2*radio*self.ValorConversion
            unique_id = f"row_{medicion_num + idx - 1}"
            self.results_table.insert("", "end", iid=unique_id, values=(medicion_num + idx - 1, f"{diametro:.2f}"))
        self.results_table.update_idletasks()
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    def estimar_parametros_por_referencia(self, tolerancia_porcentual=0.10):
        if self.ValorLongitud.get() <= 0:
            messagebox.showwarning("Advertencia", "Debe trazar una línea de referencia para medir el diámetro.")
            return None
        radio_referencia = self.ValorLongitud.get() / 2
        tolerancia = radio_referencia * tolerancia_porcentual
        min_radius = radio_referencia - tolerancia
        max_radius = radio_referencia + tolerancia
        min_dist = max_radius
        param1 = 50
        param2 = 30
        return {
            "min_radius": min_radius,
            "max_radius": max_radius,
            "min_dist": min_dist,
            "param1": param1,
            "param2": param2
        }

    # Función para detectar círculos por referencia de forma automática
    def detectar_circulos_por_referencia(self):
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada.")
            return
        self.selected_shape.set("Círculos")
        params = self.estimar_parametros_por_referencia(tolerancia_porcentual=0.10)
        if params is None:
            return
        min_radius = params["min_radius"]
        max_radius = params["max_radius"]
        min_dist = params["min_dist"]
        param1 = params["param1"]
        param2 = params["param2"]
        self.min_radius_slider.set(min_radius * 2)
        self.max_radius_slider.set(max_radius * 2)
        self.min_dist_slider.set(min_dist)
        self.param1_slider.set(param1)
        self.param2_slider.set(param2)
        self.update_min_radius(min_radius * 2)
        self.update_max_radius(max_radius * 2)
        self.update_min_dist(min_dist)
        self.update_param1(param1)
        self.update_param2(param2)
        self.apply_parameters(min_dist, param1, param2, min_radius * 2, max_radius * 2)
        self.count_contours()
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    def evaluar_deteccion(self):
        if not self.contour_original_coords or not self.manual_annotations:
            messagebox.showinfo("Evaluación", "Debe haber detección automática y anotaciones manuales.")
            return
        for obj_id in self.evaluation_canvas_ids:
            self.canvas.delete(obj_id)
        self.evaluation_canvas_ids.clear()
        auto_coords = []
        for pts, _ in self.contour_original_coords:
            xs = [x for x, y in pts]
            ys = [y for x, y in pts]
            cx, cy = np.mean(xs), np.mean(ys)
            auto_coords.append((cx, cy))
        tp = 0
        matched_auto = set()
        matched_manual = set()
        for i, (xm, ym, _) in enumerate(self.manual_annotations):
            matched = False
            for j, (xa, ya) in enumerate(auto_coords):
                dist = np.sqrt((xm - xa)**2 + (ym - ya)**2)
                if dist <= self.match_threshold and j not in matched_auto:
                    matched = True
                    tp += 1
                    matched_auto.add(j)
                    matched_manual.add(i)
                    x, y = xa*self.scale_factor + self.x_offset, ya*self.scale_factor + self.y_offset
                    cid = self.canvas.create_oval(x-5, y-5, x+5, y+5, fill="green", outline="")
                    self.evaluation_canvas_ids.append(cid)
                    break
            if not matched:
                x, y = xm*self.scale_factor + self.x_offset, ym*self.scale_factor + self.y_offset
                cid = self.canvas.create_oval(x-5, y-5, x+5, y+5, fill="blue", outline="")
                self.evaluation_canvas_ids.append(cid)
        for j, (xa, ya) in enumerate(auto_coords):
            if j not in matched_auto:
                x, y = xa*self.scale_factor + self.x_offset, ya*self.scale_factor + self.y_offset
                cid = self.canvas.create_oval(x-5, y-5, x+5, y+5, fill="red", outline="")
                self.evaluation_canvas_ids.append(cid)
        fn = len(self.manual_annotations) - tp
        fp = len(auto_coords) - tp
        precision = tp / (tp + fp) if tp + fp > 0 else 0
        recall = tp / (tp + fn) if tp + fn > 0 else 0
        f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0
        messagebox.showinfo("Resultados",
                            f"TP: {tp}\nFP: {fp}\nFN: {fn}\n\nPrecisión: {precision:.2f}\nRecall: {recall:.2f}\nF1-score: {f1:.2f}")
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    def get_valid_conversion(self):
        if not hasattr(self, "ValorConversion") or self.ValorConversion <= 0:
            self.ValorConversion = 1.0
        return self.ValorConversion

    # Función para buscar contornos similares automáticamente
    def buscar_candidatos_similares_automaticamente(self):
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada.")
            return
        self.save_state()
        img_np = np.array(self.temp_image)
        img_gray = cv2.cvtColor(img_np, cv2.COLOR_RGB2GRAY) if img_np.ndim == 3 else img_np.copy()
        conversion = self.get_valid_conversion()
        if hasattr(self, "radio_referencia_manual") and self.radio_referencia_manual is not None:
            radio_mm = self.radio_referencia_manual
            min_radius_um = radio_mm * 0.8
            max_radius_um = radio_mm * 1.2
            min_dist_um = radio_mm * 2
        else:
            min_dist_um = self.min_dist_slider.get()
            min_radius_um = self.min_radius_slider.get() / 2
            max_radius_um = self.max_radius_slider.get() / 2
        min_dist_px = int(min_dist_um / conversion)
        min_radius_px = int(min_radius_um / conversion)
        max_radius_px = int(max_radius_um / conversion)
        mejor_num = 0
        mejor_param1 = 50
        mejor_param2 = 30
        mejor_circulos = []
        for param1 in range(30, 120, 10):
            for param2 in range(10, 60, 5):
                circles = cv2.HoughCircles(
                    img_gray,
                    cv2.HOUGH_GRADIENT,
                    dp=1,
                    minDist=min_dist_px,
                    param1=param1,
                    param2=param2,
                    minRadius=min_radius_px,
                    maxRadius=max_radius_px
                )
                if circles is not None and len(circles[0]) > mejor_num:
                    mejor_num = len(circles[0])
                    mejor_param1 = param1
                    mejor_param2 = param2
                    mejor_circulos = circles
        if mejor_num == 0:
            messagebox.showinfo("Resultado", "No se encontraron contornos similares automáticamente.")
            return
        img_color = cv2.cvtColor(img_gray, cv2.COLOR_GRAY2BGR)
        for i in mejor_circulos[0, :]:
            center = (int(round(i[0])), int(round(i[1])))
            radius = int(round(i[2]))
            radio_fisico = radius * conversion
            self.add_results_to_table([radio_fisico])
            puntos = [
                (center[0] + radius * np.cos(t), center[1] + radius * np.sin(t))
                for t in np.linspace(0, 2 * np.pi, 20)
            ]
            self.contour_original_coords.append((puntos, "orange"))
            scaled = [(x * self.scale_factor + self.x_offset, y * self.scale_factor + self.y_offset) for x, y in puntos]
            plano = [c for p in scaled for c in p]
            cid = self.canvas.create_line(plano, fill="orange", width=2, smooth=True)
            self.contour_canvas_ids.append(cid)
            cv2.circle(img_color, center, radius, (0, 165, 255), 2)
        self.processed_image = cv2.cvtColor(img_color, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        self.param1_slider.set(mejor_param1)
        self.param2_slider.set(mejor_param2)
        self.update_param1(mejor_param1)
        self.update_param2(mejor_param2)
        messagebox.showinfo("Resultado", f"Se encontraron {mejor_num} contornos similares automáticamente.")
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    def estimar_parametros_por_patron(self, tolerancia_porcentual=0.1):
        if not hasattr(self, "radio_referencia_manual") or self.radio_referencia_manual is None:
            messagebox.showwarning("Referencia no definida", "Debe seleccionar primero un patrón de contorno.")
            return None
        if not hasattr(self, "ValorConversion") or self.ValorConversion <= 0:
            self.ValorConversion = 1.0
        r = self.radio_referencia_manual
        diametro = r * 2
        tol = diametro * tolerancia_porcentual
        min_radius = (diametro - tol) / 2
        max_radius = (diametro + tol) / 2
        min_dist = 0.75 * diametro
        param1 = 50
        param2 = 30
        return {
            "min_radius": min_radius,
            "max_radius": max_radius,
            "min_dist": min_dist,
            "param1": param1,
            "param2": param2
        }

    # Función para restaurar el estado si el marcado manual falla
    def restaurar_estado_marcado_fallido(self):
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        if hasattr(self, "temp_circle_id") and self.temp_circle_id is not None:
            self.canvas.delete(self.temp_circle_id)
            self.temp_circle_id = None
        self.btn_marcar.config(relief=tk.RAISED, state=tk.NORMAL, bg="lightgray")
        self.btn_buscar.config(state=tk.DISABLED)

    # Función para detectar contornos similares usando un patrón marcado manualmente
    def detectar_por_patrón_manual(self):
        self.btn_marcar.config(relief=tk.RAISED, state=tk.NORMAL, bg="lightgray")
        self.btn_buscar.config(state=tk.DISABLED)
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.temp_circle_id = None
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada.")
            self.restaurar_estado_marcado_fallido()
            return
        if not hasattr(self, "patron_intensidad_referencia") or self.patron_intensidad_referencia is None:
            messagebox.showwarning("Advertencia", "Primero marque un contorno manual como referencia.")
            self.restaurar_estado_marcado_fallido()
            return
        plantilla = self.patron_intensidad_referencia.copy().astype(np.uint8)
        if plantilla.shape[0] < 5 or plantilla.shape[1] < 5:
            messagebox.showwarning("Advertencia", "La plantilla es demasiado pequeña para la detección.")
            self.restaurar_estado_marcado_fallido()
            return
        img = np.array(self.temp_image)
        img_gray = cv2.cvtColor(img, cv2.COLOR_RGB2GRAY) if img.ndim == 3 else img.copy()
        ih, iw = img_gray.shape[:2]
        ph, pw = plantilla.shape[:2]
        if ih < ph or iw < pw:
            messagebox.showerror("Error", "La imagen es más pequeña que la plantilla.")
            self.restaurar_estado_marcado_fallido()
            return
        try:
            resultado = cv2.matchTemplate(img_gray, plantilla, cv2.TM_CCOEFF_NORMED)
        except cv2.error as e:
            messagebox.showerror("Error", f"Fallo en matchTemplate:\n{str(e)}")
            self.restaurar_estado_marcado_fallido()
            return
        umbral = 0.8
        ubicaciones = list(zip(*np.where(resultado >= umbral)))
        r_px = plantilla.shape[0] // 2
        img_color = cv2.cvtColor(img_gray, cv2.COLOR_GRAY2BGR)
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        centros_aceptados = []
        num_detectados = 0
        for (y, x) in ubicaciones:
            centro_actual = (x + r_px, y + r_px)
            if any(np.hypot(cx - centro_actual[0], cy - centro_actual[1]) < 2 * r_px for cx, cy in centros_aceptados):
                continue
            centros_aceptados.append(centro_actual)
            radio_fisico = r_px * self.ValorConversion
            self.add_results_to_table([radio_fisico])
            puntos = [
                (centro_actual[0] + r_px * np.cos(t), centro_actual[1] + r_px * np.sin(t))
                for t in np.linspace(0, 2 * np.pi, 20)
            ]
            self.contour_original_coords.append((puntos, "green"))
            scaled = [(x * self.scale_factor + self.x_offset, y * self.scale_factor + self.y_offset) for x, y in puntos]
            plano = [c for p in scaled for c in p]
            cid = self.canvas.create_line(plano, fill="green", width=2, smooth=True)
            self.contour_canvas_ids.append(cid)
            cv2.circle(img_color, centro_actual, r_px, (0, 255, 0), 2)
            num_detectados += 1
        self.processed_image = cv2.cvtColor(img_color, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        if num_detectados == 0:
            messagebox.showinfo("Resultado", "No se encontraron coincidencias.")
        else:
            messagebox.showinfo("Resultado", f"Se encontraron {num_detectados} objetos similares.")
        self.btn_buscar.config(state=tk.DISABLED)

    # Función para iniciar el marcado manual de contornos
    def iniciar_marcado_manual(self):
        if self.temp_image is None:
            messagebox.showwarning("Imagen no cargada", "Primero debe cargar una imagen.")
            return
        self.btn_marcar.config(relief=tk.SUNKEN, state=tk.DISABLED, bg="lightgreen")
        self.canvas.bind("<Button-1>", self.marcar_centro)
        self.canvas.bind("<B1-Motion>", self.ajustar_radio)
        self.canvas.bind("<ButtonRelease-1>", self.finalizar_marcado)
        self.start_x, self.start_y = None, None
        self.temp_circle_id = None

    # Funciones para el marcado manual de contornos ----------------#
    def marcar_centro(self, event):
        self.start_x, self.start_y = self.get_original_coordinates(event.x, event.y)
        x, y = self.start_x * self.scale_factor + self.x_offset, self.start_y * self.scale_factor + self.y_offset
        self.temp_circle_id = self.canvas.create_oval(x, y, x, y, outline="green", width=2)
    def ajustar_radio(self, event):
        if self.temp_circle_id is None:
            return
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        r = ((end_x - self.start_x)**2 + (end_y - self.start_y)**2)**0.5
        x0 = (self.start_x - r)*self.scale_factor + self.x_offset
        y0 = (self.start_y - r)*self.scale_factor + self.y_offset
        x1 = (self.start_x + r)*self.scale_factor + self.x_offset
        y1 = (self.start_y + r)*self.scale_factor + self.y_offset
        self.canvas.coords(self.temp_circle_id, x0, y0, x1, y1)

    # Marcado de contornos manuales ---------------------#
    def finalizar_marcado(self, event):
        if self.start_x is None or self.start_y is None:
            return
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        r = ((end_x - self.start_x)**2 + (end_y - self.start_y)**2)**0.5
        self.manual_annotations.append((self.start_x, self.start_y, r))
        self.evaluation_canvas_ids.append(self.temp_circle_id)
        self.temp_circle_id = None
        cx, cy = self.start_x, self.start_y
        r = ((end_x - self.start_x)**2 + (end_y - self.start_y)**2)**0.5
        img = np.array(self.temp_image)
        if img.ndim == 3:
            img = cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
        cx_px = int(cx)
        cy_px = int(cy)
        r_px = int(r)
        h, w = img.shape[:2]
        if r_px <= 1 or cx_px - r_px < 0 or cy_px - r_px < 0 or cx_px + r_px > w or cy_px + r_px > h:
            messagebox.showwarning("Advertencia", "El contorno está demasiado cerca del borde o es demasiado pequeño.")
            return
        mask = np.zeros_like(img, dtype=np.uint8)
        cv2.circle(mask, (cx_px, cy_px), r_px, 255, -1)
        roi = cv2.bitwise_and(img, img, mask=mask)
        x0 = max(cx_px - r_px, 0)
        y0 = max(cy_px - r_px, 0)
        x1 = min(cx_px + r_px, w)
        y1 = min(cy_px + r_px, h)
        recorte = roi[y0:y1, x0:x1]
        if recorte.size == 0 or recorte.shape[0] < 5 or recorte.shape[1] < 5:
            messagebox.showwarning("Advertencia", "El patrón extraído es demasiado pequeño o inválido.")
            return
        if not hasattr(self, "ValorConversion") or self.ValorConversion <= 0:
            self.ValorConversion = 1.0
        self.patron_intensidad_referencia = recorte.copy()
        self.radio_referencia_manual = r * self.ValorConversion
        self.btn_marcar.config(relief=tk.RAISED, state=tk.NORMAL, bg="lightgray")
        self.btn_buscar.config(state=tk.NORMAL)
        params = self.estimar_parametros_por_patron(tolerancia_porcentual=0.15)
        if params:
            min_radius = params["min_radius"]
            max_radius = params["max_radius"]
            min_dist = params["min_dist"]
            param1 = params["param1"]
            param2 = params["param2"]
            self.min_radius_slider.set(min_radius * 2)
            self.max_radius_slider.set(max_radius * 2)
            self.min_dist_slider.set(min_dist)
            self.param1_slider.set(param1)
            self.param2_slider.set(param2)
            self.update_min_radius(min_radius * 2)
            self.update_max_radius(max_radius * 2)
            self.update_min_dist(min_dist)
            self.update_param1(param1)
            self.update_param2(param2)
            self.selected_shape.set("Círculos")
            self.apply_parameters(min_dist, param1, param2, min_radius * 2, max_radius * 2)
            self.count_contours()
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    # Función para calcular estadísticas y actualizar histograma ---#
    def calculate_statistics(self, values):                         
        if not values:                                              
            tk.messagebox.showwarning("Advertencia", "No hay valores en la tabla para calcular estadísticas.")
            return                                                  
        try:
            stats = {
                "No. Datos": len(values),
                "Promedio": mean(values),
                "Desv. estándar": stdev(values) if len(values) > 1 else 0,
                "Mínimo": min(values),
                "Máximo": max(values),
            }                              
            unidad = self.distance_units_var.get()
            for widget in self.stats_frame.winfo_children():
                widget.destroy()
            for key, value in stats.items():
                if key == "No. Datos":
                    texto = f"{key}: {value}"
                else:
                    texto = f"{key}: {value:.1f} {unidad}"
                tk.Label(
                    self.stats_frame,
                    text=texto,
                    font=("Arial", 9),
                    anchor="w",
                    bg="white"
                ).pack(fill="x", padx=5, pady=1)
            for i in range(len(stats)):
                self.stats_frame.grid_rowconfigure(i, weight=1)
            for widget in self.hist_canvas.winfo_children():
                widget.destroy()         
            min_val = min(values)
            max_val = max(values)
            try:
                entry_val = self.entry_bins.get()
                if entry_val.strip():
                    k = int(entry_val)
                    if k <= 0:
                        raise ValueError
                else:
                    k = math.ceil(1 + 3.322 * math.log10(len(values)))
            except ValueError:
                tk.messagebox.showwarning("Entrada inválida", "El número de intervalos debe ser un entero positivo.")
                return
            if min_val == max_val:
                min_val -= 0.5
                max_val += 0.5
            h = (max_val - min_val) / k
            bins = [min_val + i * h for i in range(k + 1)]
            fig, ax = plt.subplots(figsize=(4.2, 2.0), dpi=100)
            n, bins_edges, _ = ax.hist(values, bins=bins, color='red', edgecolor='red', alpha=0.7, rwidth=0.8)
            media = mean(values)
            desv_std = stdev(values) if len(values) > 1 else 0.1
            x = np.linspace(min_val, max_val, 1500)
            bin_width = bins_edges[1] - bins_edges[0]
            area_total = sum(n) * bin_width
            y = norm.pdf(x, loc=media, scale=desv_std) * area_total
            ax.plot(x, y, color='blue', linewidth=2)
            ax.set_title(f"Histograma de Frecuencias ({k} clases)", fontsize=9)
            ax.set_xlabel(f"Diámetros ({unidad})", fontsize=8)
            ax.set_ylabel("Frecuencia", fontsize=8)
            ax.set_xlim(min_val, max_val)
            bin_centers = [(bins_edges[i] + bins_edges[i+1]) / 2 for i in range(len(bins_edges) - 1)]
            ax.set_xticks(bin_centers)
            ax.set_xticklabels([f"{center:.1f}" for center in bin_centers], rotation=90, fontsize=8)
            ax.tick_params(axis='y', labelsize=8)            
            ax.grid(axis='y', alpha=0.5)
            fig.tight_layout()
            canvas = FigureCanvasTkAgg(fig, master=self.hist_canvas)
            canvas.draw()
            canvas_widget = canvas.get_tk_widget()
            canvas_widget.pack(fill="both", expand=True)
            plt.close(fig)
        except Exception as e:                                      
            tk.messagebox.showerror("Error", f"Error al calcular estadísticas o generar histograma: {e}")

    def update_histogram_from_entry(self):
        values = self.get_table_values()
        if values:
            self.calculate_statistics(values)

    # Función para extraer valores de la tabla ---------------------#
    def get_table_values(self):
        values = []
        for row in self.results_table.get_children():
            diameter = self.results_table.item(row, "values")[1]
            try:
                values.append(float(diameter))
            except ValueError:
                continue
        return values
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    # Función para calcular las coordenadas para centrar una imagen ----#
    def calculate_centered_coordinates(self, img_width, img_height):
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        x = max((canvas_width - img_width) // 2, 0)
        y = max((canvas_height - img_height) // 2, 0)
        return x, y

    # Función para actualizar la imagen en el canvas redimensionada y centrada -------------#
    def update_canvas_image(self):
        if self.temp_image is None:
            return
        img_width, img_height = self.temp_image.size
        scale = self.scale_factor
        new_size = (int(img_width*scale), int(img_height*scale))
        img_resized = self.temp_image.resize(new_size, Image.Resampling.LANCZOS)
        self.img_tk = ImageTk.PhotoImage(img_resized)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=self.img_tk)
        self.canvas.image = self.img_tk
        self.canvas.config(scrollregion=self.canvas.bbox("all"))

    # Función para convertir y mostrar una imagen de OpenCV encanvas#
    def display_cv_image(self, cv_image):
        if cv_image is None or not isinstance(cv_image, np.ndarray):
            return
        rgb_image = cv2.cvtColor(cv_image, cv2.COLOR_BGR2RGB)
        pil_image = Image.fromarray(rgb_image)
        img_width, img_height = pil_image.size
        new_width = int(img_width*self.scale_factor)
        new_height = int(img_height*self.scale_factor)
        resized_img = pil_image.resize((new_width, new_height), Image.Resampling.LANCZOS)
        tk_image = ImageTk.PhotoImage(resized_img)
        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)
        self.canvas.delete("all")
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=tk_image)
        self.canvas.image = tk_image
        self.canvas.config(scrollregion=self.canvas.bbox("all"))

    # Función para iniciar el arrastre del canvas ----------#
    def start_drag(self, event):
        self.canvas.scan_mark(event.x, event.y)
        self.canvas.unbind("<ButtonPress-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.canvas.bind("<ButtonRelease-1>", self.stop_drag)

    # Función para arrastrar el canvas ---------------------#
    def drag(self, event):
        dx = event.x - self.last_x
        dy = event.y - self.last_y
        self.canvas.xview_scroll(int(-dx), "units")
        self.canvas.yview_scroll(int(-dy), "units")
        self.last_x, self.last_y = event.x, event.y

    # Función para detener el arrastre ---------------------#      
    def stop_drag(self, event):
        self.canvas.bind("<ButtonPress-1>", self.start_drag)
        self.canvas.bind("<B1-Motion>", self.drag)
        self.canvas.unbind("<ButtonRelease-1>")

    # Función para detectar el arrastre con el botón del med#
    def on_drag(self, event):
        delta_x = event.x - self.last_x
        delta_y = event.y - self.last_y
        self.canvas.xview_scroll(-delta_x, "units")
        self.canvas.yview_scroll(-delta_y, "units")
        self.last_x = event.x
        self.last_y = event.y

    # Función para el desplazamiento con la rueda del mouse
    def on_mouse_wheel(self, event):
        if event.num == 5 or event.delta < 0:
            self.canvas.yview_scroll(1, "units")
        elif event.num == 4 or event.delta > 0:
            self.canvas.yview_scroll(-1, "units")

    # Función para cargar la imagen seleccionada -------------------#                
    def load_image(self, image_path):
        self.current_image = cv2.imread(image_path)
        self.original_image = self.current_image.copy()
        img_rgb = cv2.cvtColor(self.current_image, cv2.COLOR_BGR2RGB)
        self.original_image = Image.fromarray(img_rgb)
        self.temp_image = self.original_image.copy()
        self.original_width, self.original_height = self.original_image.size
        self.temp_image = self.original_image.copy()
        self.temp_image_name = os.path.basename(image_path)
        self.show_image_in_canvas(self.original_image, self.canvas)
        self.show_image_in_canvas(self.temp_image, self.canvas_temp)
        self.display_cv_image(self.current_image)

    # Función para mostrar una imagen en el canvas -----------------#
    def show_image_in_canvas(self, image, canvas):
        if isinstance(image, Image.Image):
            img_pil = image
        else:
            if image.ndim == 3 and image.shape[-1] == 4:
                image = cv2.cvtColor(image, cv2.COLOR_RGBA2RGB)
            elif image.ndim == 2:
                image = cv2.cvtColor(image, cv2.COLOR_GRAY2RGB)
            img_rgb = cv2.cvtColor(image, cv2.COLOR_BGR2RGB)
            img_pil = Image.fromarray(img_rgb)
        if canvas == self.canvas_temp:
            canvas.update_idletasks()
            canvas_width = canvas.winfo_width()
            canvas_height = canvas.winfo_height()
            if canvas_width <= 1 or canvas_height <= 1:
                canvas.after(100, lambda: self.show_image_in_canvas(image, canvas))
                return
            scale = min(canvas_width/img_pil.width, canvas_height/img_pil.height)
            new_width = int(img_pil.width*scale)
            new_height = int(img_pil.height*scale)
            img_resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
            x = (canvas_width - new_width) // 2
            y = (canvas_height - new_height) // 2
        else:
            new_width = int(img_pil.width*self.scale_factor)
            new_height = int(img_pil.height*self.scale_factor)
            img_resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
            x, y = self.calculate_centered_coordinates(new_width, new_height)
            self.x_offset, self.y_offset = x, y
        img_tk = ImageTk.PhotoImage(img_resized)
        canvas.delete("all")
        canvas.create_image(x, y, anchor="nw", image=img_tk)
        canvas.image = img_tk
        canvas.config(scrollregion=canvas.bbox("all"))
        if canvas != self.canvas_temp:
            canvas.bind("<B2-Motion>", self.on_drag)
            canvas.bind("<Button-4>", self.on_mouse_wheel)
            canvas.bind("<Button-5>", self.on_mouse_wheel)
        else:
            canvas.unbind("<B2-Motion>")
            canvas.unbind("<Button-4>")
            canvas.unbind("<Button-5>")

    # Función para limpiar miniaturas
    def clear_thumbnails(self):
        for widget in self.thumbnail_scroll_frame.winfo_children():
            widget.destroy()
        self.image_labels.clear()
        self.image_refs.clear()
        self.selected_thumbnail_frame = None

    # Función para crear miniatura de una imagen
    def create_thumbnail(self, image_path, size=(80, 80)):
        try:
            img = cv2.imread(image_path, cv2.IMREAD_UNCHANGED)
            if img is None:
                raise ValueError("cv2 no pudo abrir la imagen.")
            if len(img.shape) == 2:
                img = cv2.cvtColor(img, cv2.COLOR_GRAY2RGB)
            elif img.shape[2] == 4:
                img = cv2.cvtColor(img, cv2.COLOR_BGRA2RGB)
            else:
                img = cv2.cvtColor(img, cv2.COLOR_BGR2RGB)
        except Exception:
            pil_img = Image.open(image_path).convert("RGB")
            img = np.array(pil_img)
        pil_img = Image.fromarray(img)
        pil_img.thumbnail(size)
        return ImageTk.PhotoImage(pil_img)

    # Función para crear una etiqueta de miniatura
    def create_image_label(self, img_tk, image_path):
        frame = tk.Frame(self.thumbnail_scroll_frame, bg=self.thumbnail_scroll_frame.cget("bg"))
        frame.image_path = image_path
        label = tk.Label(frame, image=img_tk, bg=frame.cget("bg"))
        label.img_tk = img_tk
        def on_select(event, path=image_path, this_frame=frame):
            self.selected_image_path = path
            self.load_image(path)
            self.highlight_thumbnail(this_frame)
        label.bind("<Double-Button-1>", on_select)
        label.pack(side=tk.TOP, padx=5, pady=5, anchor="n")
        name_label = tk.Label(frame, text=os.path.basename(image_path), wraplength=80, font=("Arial", 10))
        name_label.pack(side=tk.TOP, anchor="n")
        frame.pack(side=tk.LEFT, padx=5, pady=5, anchor="n")
        self.image_labels.append(label)
        self.image_refs.append(img_tk)

    # Función para resaltar la miniatura seleccionada
    def highlight_thumbnail(self, frame_to_highlight):
        try:
            if self.selected_thumbnail_frame:
                self.selected_thumbnail_frame.configure(bg=self.thumbnail_scroll_frame.cget("bg"))
                for child in self.selected_thumbnail_frame.winfo_children():
                    child.configure(bg=self.thumbnail_scroll_frame.cget("bg"))
        except tk.TclError:
            pass
        frame_to_highlight.configure(bg="#fff79a")
        for child in frame_to_highlight.winfo_children():
            child.configure(bg="#fff79a")
        self.selected_thumbnail_frame = frame_to_highlight

    # Función para mostrar las miniaturas de las imágenes en un directorio
    def display_images(self, directory):
        if self.is_loading:
            return
        selected_path = getattr(self, 'selected_image_path', None)
        self.clear_thumbnails()
        self.is_loading = True
        files = [f for f in os.listdir(directory) if f.lower().endswith(('.png', '.jpg', '.jpeg', '.bmp', '.tif', '.tiff'))]
        files.sort(key=lambda x: x.lower())
        for filename in files:
            image_path = os.path.join(directory, filename)
            img_tk = self.create_thumbnail(image_path)
            self.create_image_label(img_tk, image_path)
        if selected_path:
            for frame in self.thumbnail_scroll_frame.winfo_children():
                if hasattr(frame, 'image_path') and frame.image_path == selected_path:
                    self.highlight_thumbnail(frame)
                    break
        self.is_loading = False            

    # Función para que se deslice el slider de forma continua
    def start_adjusting(self, slider, delta, callback):
        self.stop_adjusting()
        def repeat():
            self.adjust_slider(slider, delta, callback)
            self.slider_repeat_job = self.after(400, repeat)
        repeat()

    # Función para que se ajuste el slider
    def stop_adjusting(self):
        if hasattr(self, "slider_repeat_job") and self.slider_repeat_job:
            self.after_cancel(self.slider_repeat_job)
            self.slider_repeat_job = None

    # Función para ajustar el slider
    def bind_slider_trough(self, slider, callback):
        def on_click(event):
            click_x = event.x
            widget_width = slider.winfo_width()
            min_val = slider.cget("from")
            max_val = slider.cget("to")
            value_range = max_val - min_val
            slider_middle = (slider.get() - min_val)/value_range*widget_width
            delta = +1 if click_x > slider_middle else -1
            self.start_adjusting(slider, delta, callback)
        def on_release(event):
            self.stop_adjusting()
        slider.bind("<ButtonPress-1>", on_click)
        slider.bind("<ButtonRelease-1>", on_release)

    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    # Detecta las cámaras disponibles ----------------------#
    def search_cameras(self):
        self.menu.delete(1, tk.END)
        cameras = self.detect_cameras()
        if not cameras:
            self.menu.add_command(label="No hay cámaras disponibles", state="disabled")
        else:
            for index in cameras:
                self.menu.add_command(label=f"Cámara {index}", command=lambda idx=index: self.select_camera(idx))
        if self.camera_active:
            self.menu.add_separator()
            self.menu.add_command(label="Apagar cámara", command=self.close_camera)


    # Detecta las cámaras disponibles ----------------------#       
    def detect_cameras(self):
        available_cameras = []
        for index in range(10):
            try:
                cap = cv2.VideoCapture(index)
                if cap.isOpened():
                    ret, _ = cap.read()
                    if ret:
                        available_cameras.append(index)
                cap.release()
            except:
                continue
        return available_cameras

    # Selecciona una cámara y la activa --------------------#
    def select_camera(self, camera_index):
        if self.camera_active:
            self.close_camera()
        self.start_camera(camera_index)
        self.search_cameras()

    # Inicia la cámara seleccionada -----------------------#
    def start_camera(self, camera_index):
        try:
            self.cap = cv2.VideoCapture(camera_index)
            if not self.cap.isOpened():
                messagebox.showerror("Error", f"No se pudo abrir la cámara {camera_index}")
                return
            self.camera_active = True
            self.toggle_button.config(text=f"Cámara {camera_index} (Activa)")
            self.selected_camera_index = camera_index
            self.update_frame()
        except Exception as e:
            messagebox.showerror("Error", f"Error al iniciar la cámara: {str(e)}")

    def update_frame(self):
        if self.camera_active and self.cap:
            ret, frame = self.cap.read()
            if ret:
                frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                frame = cv2.resize(frame, (self.canvas_width, self.canvas_height))
                img = Image.fromarray(frame)
                imgtk = ImageTk.PhotoImage(image=img)
                self.camera_canvas.create_image(0, 0, anchor="nw", image=imgtk)
                self.camera_canvas.image = imgtk
                self.after(10, self.update_frame)

    def close_camera(self):
        if self.cap:
            self.cap.release()
            self.cap = None 
        self.camera_active = False
        self.camera_canvas.delete("all")
        self.toggle_button.config(text="Cámara")
        self.search_cameras()
        messagebox.showinfo("Cámara", "Cámara apagada.")
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    def agregar_tooltip(self, widget, text):
        if hasattr(widget, "_tooltip_window") and widget._tooltip_window is not None:
            widget._tooltip_window.destroy()
            widget._tooltip_window = None
        tooltip = tk.Toplevel(widget)
        tooltip.withdraw()
        tooltip.overrideredirect(True)
        tooltip_label = tk.Label(tooltip, text=text, background="white", relief="solid", borderwidth=1)
        tooltip_label.pack()
        widget._tooltip_window = tooltip
        def show_tooltip(event):
            x = event.x_root + 10
            y = event.y_root + 10
            tooltip.geometry(f"+{x}+{y}")
            tooltip.deiconify()
        def hide_tooltip(event):
            tooltip.withdraw()
        widget.bind("<Enter>", show_tooltip)
        widget.bind("<Leave>", hide_tooltip)
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    def on_closing(self):
        if messagebox.askokcancel("Salir", "¿Desea salir de la aplicación?"):
            self.quit()
            self.destroy()
            os._exit(0)
if __name__ == "__main__":
    viewer = Ventana_Usuario_v5_05()
    viewer.mainloop()
